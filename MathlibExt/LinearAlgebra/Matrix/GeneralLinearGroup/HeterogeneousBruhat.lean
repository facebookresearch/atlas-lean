/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.HeterogeneousPivotReduction
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.HeterogeneousBruhatInsertion

/-!
# Heterogeneous Bruhat decomposition

This module constructs heterogeneous Bruhat decompositions of invertible
rectangular-index matrices over division rings. It exposes a canonical
decomposition into left upper-elementary, weighted permutation / monomial,
and right upper-elementary factors and proves coefficient naturality for the
canonical choice.
-/

@[expose] public section

namespace Matrix

namespace GeneralLinearEquiv

open Matrix.GeneralLinearGroup

section EmptyBridge

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable {K : Type*} [DivisionRing K]

/-- If `m` empty then `n` empty, via two-sided inverse. -/
theorem isEmpty_n_of_isEmpty_m [IsEmpty m]
    (e : GeneralLinearEquiv m n K) : IsEmpty n where
  false j := by
    have hMul : e.inv * e.val = 1 := e.inv_val
    have hEq : (e.inv * e.val) j j = (1 : Matrix n n K) j j := by rw [hMul]
    have hOne : (1 : Matrix n n K) j j = (1 : K) := by
      simp [Matrix.one_apply_eq]
    have hZero : (e.inv * e.val) j j = (0 : K) := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      exact False.elim (isEmptyElim k)
    rw [hZero, hOne] at hEq
    exact one_ne_zero hEq.symm

/-- If `n` empty then `m` empty, via two-sided inverse. -/
theorem isEmpty_m_of_isEmpty_n [IsEmpty n]
    (e : GeneralLinearEquiv m n K) : IsEmpty m where
  false i := by
    have hMul : e.val * e.inv = 1 := e.val_inv
    have hEq : (e.val * e.inv) i i = (1 : Matrix m m K) i i := by rw [hMul]
    have hOne : (1 : Matrix m m K) i i = (1 : K) := by
      simp [Matrix.one_apply_eq]
    have hZero : (e.val * e.inv) i i = (0 : K) := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      exact False.elim (isEmptyElim k)
    rw [hZero, hOne] at hEq
    exact one_ne_zero hEq.symm

/-- `IsEmpty n` follows from `card m = 0`. -/
theorem isEmpty_n_of_card_zero (e : GeneralLinearEquiv m n K)
    (h0 : Fintype.card m = 0) : IsEmpty n := by
  have hIsEmptyM : IsEmpty m := by
    rwa [Fintype.card_eq_zero_iff] at h0
  have : IsEmpty m := hIsEmptyM
  exact isEmpty_n_of_isEmpty_m e

/-- `Nonempty n` follows from `Nonempty m`. -/
theorem nonempty_n_of_nonempty_m [Nonempty m]
    (e : GeneralLinearEquiv m n K) : Nonempty n := by
  by_contra hNot
  rw [not_nonempty_iff] at hNot
  have : IsEmpty n := hNot
  have hIsEmptyM : IsEmpty m := isEmpty_m_of_isEmpty_n e
  exact not_isEmpty_of_nonempty m hIsEmptyM

end EmptyBridge

section SquareBridge

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {K : Type*} [DivisionRing K]

/-- Square bridge: `extendByIdentity` equals `insertEntryEquiv c c 1`. -/
theorem ofGL_extendByIdentity_eq_insert (c : ι) (g : GL (DeletedIndex ι c) K) :
    ofGL (Matrix.GeneralLinearGroup.extendByIdentity
      (Matrix.GeneralLinearGroup.deletedOrderEmbedding c) g) =
      insertEntryEquiv (m := ι) (n := ι) c c 1 (ofGL g) := by
  apply ext
  have hToGL :=
    toGL_insertEntryEquiv_one_ofGL_eq_extendByIdentity (R := K) c g
  have hInv : ofGL (Matrix.GeneralLinearGroup.extendByIdentity
      (Matrix.GeneralLinearGroup.deletedOrderEmbedding c) g) =
      ofGL (toGL (insertEntryEquiv c c 1 (ofGL g))) := by rw [hToGL]
  rw [hInv, ofGL_toGL]

/-- Bundled upper-elementary bridge. -/
theorem ofGL_upper_extendByIdentity_eq_insert (c : ι)
    (g : upperElementarySubgroup (DeletedIndex ι c) K) :
    ofGL ((Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
      (Matrix.GeneralLinearGroup.deletedOrderEmbedding c) g).val) =
      insertEntryEquiv (m := ι) (n := ι) c c 1 (ofGL g.val) := by
  have hGL : (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
      (Matrix.GeneralLinearGroup.deletedOrderEmbedding c) g).val =
      Matrix.GeneralLinearGroup.extendByIdentity
        (Matrix.GeneralLinearGroup.deletedOrderEmbedding c) g.val := by
    simp [Matrix.GeneralLinearGroup.UpperElementary.coe_extendByIdentity]
  rw [hGL]
  exact ofGL_extendByIdentity_eq_insert c g.val

end SquareBridge

section BruhatStruct

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

/-- Heterogeneous Bruhat decomposition for `e : GL(m,n,K)`. -/
structure HeterogeneousBruhatDecomposition (e : GeneralLinearEquiv m n K) where
  /-- Left factor in `U m K`. -/
  left : upperElementarySubgroup m K
  /-- Diagonal weights `m → Kˣ`. -/
  weights : m → Kˣ
  /-- Permutation `n ≃ m`. -/
  perm : n ≃ m
  /-- Right factor in `U n K`. -/
  right : upperElementarySubgroup n K
  /-- Fixed left-associated factorization
  `e = ((left.trans middle).trans right)`. -/
  factorization :
    e = ((ofGL (left : GL m K)).trans (monomialEquiv weights perm)).trans
          (ofGL (right : GL n K))

namespace HeterogeneousBruhatDecomposition

/-- Value projection `e.val = L.val * monomial.val * R.val`. -/
theorem val_eq {e : GeneralLinearEquiv m n K}
    (d : HeterogeneousBruhatDecomposition e) :
    e.val = (d.left : GL m K).val * (monomialEquiv d.weights d.perm).val *
        (d.right : GL n K).val := by
  have h := congrArg GeneralLinearEquiv.val d.factorization
  simp only [val_trans] at h
  exact h

/-- Inverse projection. -/
theorem inv_eq {e : GeneralLinearEquiv m n K}
    (d : HeterogeneousBruhatDecomposition e) :
    e.inv = (d.right : GL n K)⁻¹.val *
        ((monomialEquiv d.weights d.perm).inv *
          (d.left : GL m K)⁻¹.val) := by
  have h := congrArg GeneralLinearEquiv.inv d.factorization
  simp only [inv_trans] at h
  exact h

/-- Middle monomial equivalence. -/
noncomputable def middleMonomial {e : GeneralLinearEquiv m n K}
    (d : HeterogeneousBruhatDecomposition e) : GeneralLinearEquiv m n K :=
  monomialEquiv d.weights d.perm

/-- Left square equivalence `ofGL left`. -/
noncomputable def leftEquiv {e : GeneralLinearEquiv m n K}
    (d : HeterogeneousBruhatDecomposition e) : GeneralLinearEquiv m m K :=
  ofGL (d.left : GL m K)

/-- Right square equivalence `ofGL right`. -/
noncomputable def rightEquiv {e : GeneralLinearEquiv m n K}
    (d : HeterogeneousBruhatDecomposition e) : GeneralLinearEquiv n n K :=
  ofGL (d.right : GL n K)

private theorem map_ofGL {ι : Type*} [DecidableEq ι] [Fintype ι]
    {K L : Type*} [DivisionRing K] [DivisionRing L]
    (f : K →+* L) (g : GL ι K) :
    (ofGL g).map f = ofGL (Matrix.GeneralLinearGroup.mapRingHom f g) := by
  apply ext
  rfl

/-- Coefficient-functorial image of a heterogeneous Bruhat decomposition.

Given `f : K →+* L`, `e : GeneralLinearEquiv m n K` and
`d : HeterogeneousBruhatDecomposition e` with factorization
`e = ((ofGL left).trans (monomialEquiv weights perm)).trans (ofGL right)`,
`d.map f` is the decomposition of `e.map f` whose left/right factors are
`UpperElementary.mapRingHom f left/right`, whose weights are
`Units.map f ∘ weights`, whose permutation is the same, and whose
factorization follows from `d.factorization`, `GeneralLinearEquiv.map_trans`,
`GeneralLinearEquiv.map_monomialEquiv`, and the GL/upper map lemmas.
This maps an arbitrary decomposition only; no claim about the canonical
choice `heterogeneousBruhatDecomposition` is made. -/
def map {K L : Type*} [DivisionRing K] [DivisionRing L]
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n]
    (f : K →+* L) {e : GeneralLinearEquiv m n K}
    (d : HeterogeneousBruhatDecomposition e) :
    HeterogeneousBruhatDecomposition (e.map f) where
  left := Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f d.left
  weights := fun i => Units.map f (d.weights i)
  perm := d.perm
  right := Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f d.right
  factorization := by
    have hFact := d.factorization
    have hOfGLLeft : (ofGL (d.left : GL m K)).map f =
        ofGL (Matrix.GeneralLinearGroup.mapRingHom f (d.left : GL m K)) :=
      map_ofGL f _
    have hOfGLRight : (ofGL (d.right : GL n K)).map f =
        ofGL (Matrix.GeneralLinearGroup.mapRingHom f (d.right : GL n K)) :=
      map_ofGL f _
    have hGLLeft : Matrix.GeneralLinearGroup.mapRingHom f (d.left : GL m K) =
        (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f d.left :
          GL m L) :=
      (Matrix.GeneralLinearGroup.UpperElementary.coe_mapRingHom f d.left).symm
    have hGLRight : Matrix.GeneralLinearGroup.mapRingHom f (d.right : GL n K) =
        (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f d.right :
          GL n L) :=
      (Matrix.GeneralLinearGroup.UpperElementary.coe_mapRingHom f d.right).symm
    calc e.map f =
        (((ofGL (d.left : GL m K)).trans
          (monomialEquiv d.weights d.perm)).trans
          (ofGL (d.right : GL n K))).map f :=
      congrArg (fun q : GeneralLinearEquiv m n K => q.map f) hFact
      _ = (((ofGL (d.left : GL m K)).trans
            (monomialEquiv d.weights d.perm)).map f).trans
          ((ofGL (d.right : GL n K)).map f) := by
          rw [GeneralLinearEquiv.map_trans]
      _ = (((ofGL (d.left : GL m K)).map f).trans
            ((monomialEquiv d.weights d.perm).map f)).trans
          ((ofGL (d.right : GL n K)).map f) := by
          rw [GeneralLinearEquiv.map_trans]
      _ = (((ofGL (d.left : GL m K)).map f).trans
            (monomialEquiv (fun i => Units.map f (d.weights i))
              d.perm)).trans
          ((ofGL (d.right : GL n K)).map f) := by
          rw [GeneralLinearEquiv.map_monomialEquiv]
      _ = ((ofGL (Matrix.GeneralLinearGroup.mapRingHom f
            (d.left : GL m K))).trans
            (monomialEquiv (fun i => Units.map f (d.weights i))
              d.perm)).trans
          ((ofGL (d.right : GL n K)).map f) := by rw [hOfGLLeft]
      _ = ((ofGL (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f
            d.left : GL m L)).trans
            (monomialEquiv (fun i => Units.map f (d.weights i))
              d.perm)).trans
          ((ofGL (d.right : GL n K)).map f) := by rw [hGLLeft]
      _ = ((ofGL (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f
            d.left : GL m L)).trans
            (monomialEquiv (fun i => Units.map f (d.weights i))
              d.perm)).trans
          (ofGL (Matrix.GeneralLinearGroup.mapRingHom f
            (d.right : GL n K))) := by rw [hOfGLRight]
      _ = ((ofGL (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f
            d.left : GL m L)).trans
            (monomialEquiv (fun i => Units.map f (d.weights i))
              d.perm)).trans
          (ofGL (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f
            d.right : GL n L)) := by rw [hGLRight]

end HeterogeneousBruhatDecomposition

end BruhatStruct

section EmptyDecomp

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

omit [LinearOrder m] [LinearOrder n] in
/-- Monomial equals any equiv when `m` empty. -/
theorem monomialEquiv_of_isEmpty_m [IsEmpty m] (w : m → Kˣ) (σ : n ≃ m)
    (e : GeneralLinearEquiv m n K) : monomialEquiv w σ = e := by
  apply ext
  ext i
  exact False.elim (isEmptyElim i)

/-- Empty Bruhat decomposition when both index types are empty. -/
noncomputable def emptyBruhatDecomposition [IsEmpty m] [IsEmpty n]
    (e : GeneralLinearEquiv m n K) : HeterogeneousBruhatDecomposition e where
  left := 1
  weights := fun i => isEmptyElim i
  perm := Equiv.equivOfIsEmpty n m
  right := 1
  factorization := by
    have hME : monomialEquiv (fun i : m => isEmptyElim i)
        (Equiv.equivOfIsEmpty n m) = e :=
      monomialEquiv_of_isEmpty_m _ _ e
    have hLeft : ofGL ((1 : upperElementarySubgroup m K) : GL m K) =
        (refl : GeneralLinearEquiv m m K) := by
      apply ext
      rfl
    have hRight : ofGL ((1 : upperElementarySubgroup n K) : GL n K) =
        (refl : GeneralLinearEquiv n n K) := by
      apply ext
      rfl
    have hRHS :
        ((ofGL ((1 : upperElementarySubgroup m K) : GL m K)).trans
          (monomialEquiv (fun i : m => isEmptyElim i)
            (Equiv.equivOfIsEmpty n m))).trans
          (ofGL ((1 : upperElementarySubgroup n K) : GL n K)) =
          monomialEquiv (fun i : m => isEmptyElim i)
            (Equiv.equivOfIsEmpty n m) := by
      rw [hLeft, hRight, refl_trans, trans_refl]
    calc e = monomialEquiv (fun i : m => isEmptyElim i)
          (Equiv.equivOfIsEmpty n m) := hME.symm
      _ = ((ofGL ((1 : upperElementarySubgroup m K) : GL m K)).trans
            (monomialEquiv (fun i : m => isEmptyElim i)
              (Equiv.equivOfIsEmpty n m))).trans
            (ofGL ((1 : upperElementarySubgroup n K) : GL n K)) :=
          hRHS.symm

/-- Empty decomposition from `card m = 0` via the empty bridge. -/
noncomputable def emptyDecompositionOfCardZero
    (e : GeneralLinearEquiv m n K) (h0 : Fintype.card m = 0) :
    HeterogeneousBruhatDecomposition e := by
  have hIsEmptyM : IsEmpty m := by
    rwa [Fintype.card_eq_zero_iff] at h0
  have : IsEmpty m := hIsEmptyM
  have hIsEmptyN : IsEmpty n := isEmpty_n_of_isEmpty_m e
  have : IsEmpty n := hIsEmptyN
  exact emptyBruhatDecomposition e

end EmptyDecomp

section Inductive

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

/-- Reusable private nonzero-branch builder for the canonical decomposition.

Given `e : GL m n K` with `Nonempty n`, hence `Nonempty m`, and a recursive
decomposition `recDec` of `reducedPivotEquiv e`, assemble the canonical
decomposition of `e` as `leftClear⁻¹ * leftEmb`, inserted weights/permutation,
and `rightEmb * rightClear⁻¹`.  This is exactly the former monolithic branch
factored into a private helper for stable unfolding. -/
private noncomputable def heterogeneousBruhatDecompositionAux_build
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] {K : Type*} [DivisionRing K]
    [Nonempty n]
    (e : GeneralLinearEquiv m n K)
    (recDec : HeterogeneousBruhatDecomposition
      (@reducedPivotEquiv m n _ _ _ _ _ _ ‹Nonempty n› K _ e)) :
    HeterogeneousBruhatDecomposition e :=
  let c : n := @canonicalColumn n _ _ ‹Nonempty n›
  let r : m := @canonicalPivotRow m n _ _ _ _ _ _ ‹Nonempty n› K _ e
  have hp : e.val r c ≠ 0 :=
    @canonicalPivotRow_ne_zero m n _ _ _ _ _ _ ‹Nonempty n› K _ e
  let E0 : GeneralLinearEquiv m n K :=
    @canonicalPivotCleared m n _ _ _ _ _ _ ‹Nonempty n› K _ e
  let a0 : Kˣ := @canonicalPivotUnit m n _ _ _ _ _ _ ‹Nonempty n› K _ e
  let eRed : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) K :=
    @reducedPivotEquiv m n _ _ _ _ _ _ ‹Nonempty n› K _ e
  have hRecon : insertEntryEquiv r c a0 eRed = E0 :=
    @canonical_reconstruction m n _ _ _ _ _ _ ‹Nonempty n› K _ e
  have hFact : e = ((ofGL (rowClear e.val r c hp)).symm.trans E0).trans
        (ofGL (columnClear e.val r c hp)).symm :=
    @canonical_factorization m n _ _ _ _ _ _ ‹Nonempty n› K _ e
  let leftRec : upperElementarySubgroup (DeletedIndex m r) K := recDec.left
  let rightRec : upperElementarySubgroup (DeletedIndex n c) K := recDec.right
  let uRec : DeletedIndex m r → Kˣ := recDec.weights
  let σRec : DeletedIndex n c ≃ DeletedIndex m r := recDec.perm
  have hRedFac : eRed =
      ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans
        (monomialEquiv uRec σRec)).trans
        (ofGL (rightRec : GL (DeletedIndex n c) K)) :=
    recDec.factorization
  let leftEmb : upperElementarySubgroup m K :=
    Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
      (Matrix.GeneralLinearGroup.deletedOrderEmbedding r) leftRec
  let rightEmb : upperElementarySubgroup n K :=
    Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
      (Matrix.GeneralLinearGroup.deletedOrderEmbedding c) rightRec
  let leftClear : upperElementarySubgroup m K :=
    leftUpperFactor e r c hp
  let rightClear : upperElementarySubgroup n K :=
    rightUpperFactor e r c hp
  have hLeftEmbInsert : ofGL (leftEmb : GL m K) =
      insertEntryEquiv r r 1 (ofGL (leftRec : GL (DeletedIndex m r) K)) :=
    ofGL_upper_extendByIdentity_eq_insert r leftRec
  have hRightEmbInsert : ofGL (rightEmb : GL n K) =
      insertEntryEquiv c c 1
        (ofGL (rightRec : GL (DeletedIndex n c) K)) :=
    ofGL_upper_extendByIdentity_eq_insert c rightRec
  let monoRec : GeneralLinearEquiv (DeletedIndex m r)
      (DeletedIndex n c) K := monomialEquiv uRec σRec
  let monoIns : GeneralLinearEquiv m n K :=
    monomialEquiv (insertWeights r a0 uRec) (insertEquiv r c σRec)
  have hMonoRecDef : monoRec = monomialEquiv uRec σRec := rfl
  have hInsEqMono : insertEntryEquiv r c a0 monoRec = monoIns :=
    insertEntryEquiv_monomialEquiv r c a0 uRec σRec
  have hMonoEqIns : monoIns = insertEntryEquiv r c a0 monoRec :=
    hInsEqMono.symm
  have hTransLRBase :
      (insertEntryEquiv r r (1 : Kˣ) (ofGL (leftRec : GL (DeletedIndex m r) K))).trans
        (insertEntryEquiv r c a0 monoRec) =
        insertEntryEquiv r c ((1 : Kˣ) * a0)
          ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) :=
    insertEntryEquiv_trans r r c (1 : Kˣ) a0
      (ofGL (leftRec : GL (DeletedIndex m r) K)) monoRec
  have hTransLR : (insertEntryEquiv r r (1 : Kˣ)
        (ofGL (leftRec : GL (DeletedIndex m r) K))).trans monoIns =
        insertEntryEquiv r c a0
          ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) := by
    calc (insertEntryEquiv r r (1 : Kˣ)
          (ofGL (leftRec : GL (DeletedIndex m r) K))).trans monoIns
        = (insertEntryEquiv r r (1 : Kˣ)
            (ofGL (leftRec : GL (DeletedIndex m r) K))).trans
            (insertEntryEquiv r c a0 monoRec) := by rw [hMonoEqIns]
      _ = insertEntryEquiv r c ((1 : Kˣ) * a0)
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) :=
            hTransLRBase
      _ = insertEntryEquiv r c a0
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) := by
            rw [one_mul]
  have hTransRBase :
      (insertEntryEquiv r c a0 monoRec).trans
        (insertEntryEquiv c c (1 : Kˣ)
          (ofGL (rightRec : GL (DeletedIndex n c) K))) =
        insertEntryEquiv r c (a0 * 1)
          (monoRec.trans (ofGL (rightRec : GL (DeletedIndex n c) K))) :=
    insertEntryEquiv_trans r c c a0 (1 : Kˣ) monoRec
      (ofGL (rightRec : GL (DeletedIndex n c) K))
  have hTransR : monoIns.trans
        (insertEntryEquiv c c (1 : Kˣ)
          (ofGL (rightRec : GL (DeletedIndex n c) K))) =
        insertEntryEquiv r c a0
          (monoRec.trans (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
    calc monoIns.trans
          (insertEntryEquiv c c (1 : Kˣ)
            (ofGL (rightRec : GL (DeletedIndex n c) K)))
        = (insertEntryEquiv r c a0 monoRec).trans
            (insertEntryEquiv c c (1 : Kˣ)
              (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
            rw [hMonoEqIns]
      _ = insertEntryEquiv r c (a0 * 1)
            (monoRec.trans (ofGL (rightRec : GL (DeletedIndex n c) K))) :=
            hTransRBase
      _ = insertEntryEquiv r c a0
            (monoRec.trans (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
            rw [mul_one]
  have hTransMidBase :
      (insertEntryEquiv r c a0
          ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
        (insertEntryEquiv c c (1 : Kˣ)
          (ofGL (rightRec : GL (DeletedIndex n c) K))) =
        insertEntryEquiv r c (a0 * 1)
          (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
            (ofGL (rightRec : GL (DeletedIndex n c) K))) :=
    insertEntryEquiv_trans r c c a0 (1 : Kˣ)
      ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)
      (ofGL (rightRec : GL (DeletedIndex n c) K))
  have hTransMid :
      (insertEntryEquiv r c a0
          ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
        (insertEntryEquiv c c (1 : Kˣ)
          (ofGL (rightRec : GL (DeletedIndex n c) K))) =
        insertEntryEquiv r c a0
          (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
            (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
    calc (insertEntryEquiv r c a0
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
          (insertEntryEquiv c c (1 : Kˣ)
            (ofGL (rightRec : GL (DeletedIndex n c) K)))
        = insertEntryEquiv r c (a0 * 1)
            (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
              (ofGL (rightRec : GL (DeletedIndex n c) K))) := hTransMidBase
      _ = insertEntryEquiv r c a0
            (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
              (ofGL (rightRec : GL (DeletedIndex n c) K))) := by rw [mul_one]
  have hE0Eq : E0 =
        ((ofGL (leftEmb : GL m K)).trans monoIns).trans
          (ofGL (rightEmb : GL n K)) := by
    have h1 : E0 = insertEntryEquiv r c a0 eRed := hRecon.symm
    have h2 : eRed =
        ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
          (ofGL (rightRec : GL (DeletedIndex n c) K)) := by
      calc eRed = ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans
              (monomialEquiv uRec σRec)).trans
              (ofGL (rightRec : GL (DeletedIndex n c) K)) := hRedFac
        _ = ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
              (ofGL (rightRec : GL (DeletedIndex n c) K)) := by
            rw [hMonoRecDef]
    have h3 : insertEntryEquiv r c a0 eRed =
        insertEntryEquiv r c a0
          (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
            (ofGL (rightRec : GL (DeletedIndex n c) K))) := by rw [h2]
    have h4 : (ofGL (leftEmb : GL m K)).trans monoIns =
        insertEntryEquiv r c a0
          ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) := by
      calc (ofGL (leftEmb : GL m K)).trans monoIns
          = (insertEntryEquiv r r (1 : Kˣ)
              (ofGL (leftRec : GL (DeletedIndex m r) K))).trans monoIns := by
              rw [hLeftEmbInsert]
        _ = insertEntryEquiv r c a0
              ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) :=
              hTransLR
    have h5 : ((ofGL (leftEmb : GL m K)).trans monoIns).trans
          (ofGL (rightEmb : GL n K)) =
        (insertEntryEquiv r c a0
          ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
          (insertEntryEquiv c c (1 : Kˣ)
            (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
      calc ((ofGL (leftEmb : GL m K)).trans monoIns).trans
            (ofGL (rightEmb : GL n K))
          = (insertEntryEquiv r c a0
              ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
              (ofGL (rightEmb : GL n K)) := by rw [h4]
        _ = (insertEntryEquiv r c a0
              ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
              (insertEntryEquiv c c (1 : Kˣ)
                (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
              rw [hRightEmbInsert]
    calc E0 = insertEntryEquiv r c a0 eRed := h1
      _ = insertEntryEquiv r c a0
            (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
              (ofGL (rightRec : GL (DeletedIndex n c) K))) := h3
      _ = (insertEntryEquiv r c a0
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
            (insertEntryEquiv c c (1 : Kˣ)
              (ofGL (rightRec : GL (DeletedIndex n c) K))) := hTransMid.symm
      _ = ((ofGL (leftEmb : GL m K)).trans monoIns).trans
            (ofGL (rightEmb : GL n K)) := h5.symm
  let leftTotal : upperElementarySubgroup m K := leftClear⁻¹ * leftEmb
  let rightTotal : upperElementarySubgroup n K := rightEmb * rightClear⁻¹
  have hOfGLLeft : (ofGL (rowClear e.val r c hp)).symm =
      ofGL (leftClear⁻¹ : upperElementarySubgroup m K).val := by
    have : (leftClear⁻¹ : upperElementarySubgroup m K).val =
        (rowClear e.val r c hp)⁻¹ := by simp [leftClear]
    rw [this]
    rfl
  have hOfGLRight : (ofGL (columnClear e.val r c hp)).symm =
      ofGL (rightClear⁻¹ : upperElementarySubgroup n K).val := by
    have : (rightClear⁻¹ : upperElementarySubgroup n K).val =
        (columnClear e.val r c hp)⁻¹ := by simp [rightClear]
    rw [this]
    rfl
  have hFinal : e =
      ((ofGL (leftTotal : GL m K)).trans monoIns).trans
        (ofGL (rightTotal : GL n K)) := by
    have hCanon : E0 =
        ((ofGL (leftEmb : GL m K)).trans monoIns).trans
          (ofGL (rightEmb : GL n K)) := hE0Eq
    have hStep1 : e =
        ((ofGL (rowClear e.val r c hp)).symm.trans E0).trans
          (ofGL (columnClear e.val r c hp)).symm := hFact
    have hStep2 : (ofGL (rowClear e.val r c hp)).symm.trans E0 =
        (ofGL (rowClear e.val r c hp)).symm.trans
          (((ofGL (leftEmb : GL m K)).trans monoIns).trans
            (ofGL (rightEmb : GL n K))) := by rw [hCanon]
    have hStep3 : ((ofGL (rowClear e.val r c hp)).symm.trans
          (((ofGL (leftEmb : GL m K)).trans monoIns).trans
              (ofGL (rightEmb : GL n K)))).trans
          (ofGL (columnClear e.val r c hp)).symm =
        (((ofGL (rowClear e.val r c hp)).symm.trans
          (ofGL (leftEmb : GL m K))).trans monoIns).trans
          ((ofGL (rightEmb : GL n K)).trans
            (ofGL (columnClear e.val r c hp)).symm) := by
      have hAssoc1 : (ofGL (rowClear e.val r c hp)).symm.trans
            (((ofGL (leftEmb : GL m K)).trans monoIns).trans
              (ofGL (rightEmb : GL n K))) =
            ((ofGL (rowClear e.val r c hp)).symm.trans
              ((ofGL (leftEmb : GL m K)).trans monoIns)).trans
              (ofGL (rightEmb : GL n K)) := by
        rw [← trans_assoc]
      have hAssoc2 : (ofGL (rowClear e.val r c hp)).symm.trans
            ((ofGL (leftEmb : GL m K)).trans monoIns) =
            ((ofGL (rowClear e.val r c hp)).symm.trans
              (ofGL (leftEmb : GL m K))).trans monoIns := by
        rw [← trans_assoc]
      calc ((ofGL (rowClear e.val r c hp)).symm.trans
            (((ofGL (leftEmb : GL m K)).trans monoIns).trans
              (ofGL (rightEmb : GL n K)))).trans
            (ofGL (columnClear e.val r c hp)).symm
          = ((((ofGL (rowClear e.val r c hp)).symm.trans
              ((ofGL (leftEmb : GL m K)).trans monoIns)).trans
              (ofGL (rightEmb : GL n K)))).trans
              (ofGL (columnClear e.val r c hp)).symm := by rw [hAssoc1]
        _ = (((((ofGL (rowClear e.val r c hp)).symm.trans
              (ofGL (leftEmb : GL m K))).trans monoIns).trans
              (ofGL (rightEmb : GL n K)))).trans
              (ofGL (columnClear e.val r c hp)).symm := by rw [hAssoc2]
        _ = (((ofGL (rowClear e.val r c hp)).symm.trans
              (ofGL (leftEmb : GL m K))).trans monoIns).trans
              ((ofGL (rightEmb : GL n K)).trans
                (ofGL (columnClear e.val r c hp)).symm) := by
            rw [trans_assoc, trans_assoc]
    have hL : (ofGL (rowClear e.val r c hp)).symm.trans
          (ofGL (leftEmb : GL m K)) = ofGL (leftTotal : GL m K) := by
      rw [hOfGLLeft]
      apply ext
      simp [leftTotal, ofGL]
    have hR : (ofGL (rightEmb : GL n K)).trans
          (ofGL (columnClear e.val r c hp)).symm =
          ofGL (rightTotal : GL n K) := by
      rw [hOfGLRight]
      apply ext
      simp [rightTotal, ofGL]
    calc e = ((ofGL (rowClear e.val r c hp)).symm.trans E0).trans
            (ofGL (columnClear e.val r c hp)).symm := hStep1
      _ = ((ofGL (rowClear e.val r c hp)).symm.trans
            (((ofGL (leftEmb : GL m K)).trans monoIns).trans
              (ofGL (rightEmb : GL n K)))).trans
            (ofGL (columnClear e.val r c hp)).symm := by rw [hStep2]
      _ = (((ofGL (rowClear e.val r c hp)).symm.trans
            (ofGL (leftEmb : GL m K))).trans monoIns).trans
            ((ofGL (rightEmb : GL n K)).trans
              (ofGL (columnClear e.val r c hp)).symm) := hStep3
      _ = ((ofGL (leftTotal : GL m K)).trans monoIns).trans
            (ofGL (rightTotal : GL n K)) := by rw [hL, hR]
  { left := leftTotal
    weights := insertWeights r a0 uRec
    perm := insertEquiv r c σRec
    right := rightTotal
    factorization := hFinal }

private theorem heterogeneousBruhatDecompositionAux_build_left
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] {K : Type*} [DivisionRing K]
    [Nonempty n]
    (e : GeneralLinearEquiv m n K)
    (recDec : HeterogeneousBruhatDecomposition
      (@reducedPivotEquiv m n _ _ _ _ _ _ ‹Nonempty n› K _ e)) :
    (heterogeneousBruhatDecompositionAux_build e recDec).left =
      (leftUpperFactor e (canonicalPivotRow e) (canonicalColumn : n)
        (canonicalPivotRow_ne_zero e))⁻¹ *
      Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
        (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e))
        recDec.left := rfl

private theorem heterogeneousBruhatDecompositionAux_build_weights
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] {K : Type*} [DivisionRing K]
    [Nonempty n]
    (e : GeneralLinearEquiv m n K)
    (recDec : HeterogeneousBruhatDecomposition
      (@reducedPivotEquiv m n _ _ _ _ _ _ ‹Nonempty n› K _ e)) :
    (heterogeneousBruhatDecompositionAux_build e recDec).weights =
      insertWeights (canonicalPivotRow e) (canonicalPivotUnit e) recDec.weights := rfl

private theorem heterogeneousBruhatDecompositionAux_build_perm
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] {K : Type*} [DivisionRing K]
    [Nonempty n]
    (e : GeneralLinearEquiv m n K)
    (recDec : HeterogeneousBruhatDecomposition
      (@reducedPivotEquiv m n _ _ _ _ _ _ ‹Nonempty n› K _ e)) :
    (heterogeneousBruhatDecompositionAux_build e recDec).perm =
      insertEquiv (canonicalPivotRow e) (canonicalColumn : n) recDec.perm := rfl

private theorem heterogeneousBruhatDecompositionAux_build_right
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] {K : Type*} [DivisionRing K]
    [Nonempty n]
    (e : GeneralLinearEquiv m n K)
    (recDec : HeterogeneousBruhatDecomposition
      (@reducedPivotEquiv m n _ _ _ _ _ _ ‹Nonempty n› K _ e)) :
    (heterogeneousBruhatDecompositionAux_build e recDec).right =
      Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
        (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n))
        recDec.right *
      (rightUpperFactor e (canonicalPivotRow e) (canonicalColumn : n)
        (canonicalPivotRow_ne_zero e))⁻¹ := rfl

/-- Direct structural recursion on `card m` for the canonical decomposition.

This refactors the former `strongRecOn` into plain `Nat.rec` with a reusable
private nonzero-branch equation `heterogeneousBruhatDecompositionAux_build`.
The zero case is `emptyDecompositionOfCardZero`. The successor case extracts
the canonical column/row, clears, recurses on the deleted pivot, and
reassembles via `heterogeneousBruhatDecompositionAux_build`. This gives
stable unfolding for the coefficient-naturality proof. -/
noncomputable def heterogeneousBruhatDecompositionAux (k : Nat)
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] {K : Type*} [DivisionRing K]
    (e : GeneralLinearEquiv m n K) (hCard : Fintype.card m = k) :
    HeterogeneousBruhatDecomposition e :=
  match k with
  | 0 => emptyDecompositionOfCardZero e hCard
  | Nat.succ k =>
    have hCardPos : 0 < Fintype.card m := by omega
    have hNonemptyM : Nonempty m := by
      have hEquiv : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
      have hFin : Nonempty (Fin (Fintype.card m)) := ⟨⟨0, hCardPos⟩⟩
      exact ⟨hEquiv.symm hFin.some⟩
    have hNonemptyN : Nonempty n := by
      have : Nonempty m := hNonemptyM
      exact nonempty_n_of_nonempty_m e
    haveI : Nonempty m := hNonemptyM
    haveI : Nonempty n := hNonemptyN
    have hDelCard : Fintype.card (DeletedIndex m
        (@canonicalPivotRow m n _ _ _ _ _ _ ‹Nonempty n› K _ e)) = k := by
      have hDel : Fintype.card (DeletedIndex m
          (@canonicalPivotRow m n _ _ _ _ _ _ ‹Nonempty n› K _ e)) =
          Fintype.card m - 1 :=
        Matrix.GeneralLinearGroup.card_DeletedIndex
          (@canonicalPivotRow m n _ _ _ _ _ _ ‹Nonempty n› K _ e)
      omega
    let c : n := @canonicalColumn n _ _ ‹Nonempty n›
    let r : m := @canonicalPivotRow m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    have hp : e.val r c ≠ 0 :=
      @canonicalPivotRow_ne_zero m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    let E0 : GeneralLinearEquiv m n K :=
      @canonicalPivotCleared m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    let a0 : Kˣ := @canonicalPivotUnit m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    let eRed : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) K :=
      @reducedPivotEquiv m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    have hRecon : insertEntryEquiv r c a0 eRed = E0 :=
      @canonical_reconstruction m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    have hFact : e = ((ofGL (rowClear e.val r c hp)).symm.trans E0).trans
          (ofGL (columnClear e.val r c hp)).symm :=
      @canonical_factorization m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    let recDec : HeterogeneousBruhatDecomposition eRed :=
      heterogeneousBruhatDecompositionAux k eRed hDelCard
    let leftRec : upperElementarySubgroup (DeletedIndex m r) K := recDec.left
    let rightRec : upperElementarySubgroup (DeletedIndex n c) K := recDec.right
    let uRec : DeletedIndex m r → Kˣ := recDec.weights
    let σRec : DeletedIndex n c ≃ DeletedIndex m r := recDec.perm
    have hRedFac : eRed =
        ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans
          (monomialEquiv uRec σRec)).trans
          (ofGL (rightRec : GL (DeletedIndex n c) K)) :=
      recDec.factorization
    let leftEmb : upperElementarySubgroup m K :=
      Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
        (Matrix.GeneralLinearGroup.deletedOrderEmbedding r) leftRec
    let rightEmb : upperElementarySubgroup n K :=
      Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
        (Matrix.GeneralLinearGroup.deletedOrderEmbedding c) rightRec
    let leftClear : upperElementarySubgroup m K :=
      leftUpperFactor e r c hp
    let rightClear : upperElementarySubgroup n K :=
      rightUpperFactor e r c hp
    have hLeftEmbInsert : ofGL (leftEmb : GL m K) =
        insertEntryEquiv r r 1 (ofGL (leftRec : GL (DeletedIndex m r) K)) :=
      ofGL_upper_extendByIdentity_eq_insert r leftRec
    have hRightEmbInsert : ofGL (rightEmb : GL n K) =
        insertEntryEquiv c c 1
          (ofGL (rightRec : GL (DeletedIndex n c) K)) :=
      ofGL_upper_extendByIdentity_eq_insert c rightRec
    let monoRec : GeneralLinearEquiv (DeletedIndex m r)
        (DeletedIndex n c) K := monomialEquiv uRec σRec
    let monoIns : GeneralLinearEquiv m n K :=
      monomialEquiv (insertWeights r a0 uRec) (insertEquiv r c σRec)
    have hInsEqMono : insertEntryEquiv r c a0 monoRec = monoIns :=
      insertEntryEquiv_monomialEquiv r c a0 uRec σRec
    have hMonoEqIns : monoIns = insertEntryEquiv r c a0 monoRec :=
      hInsEqMono.symm
    have hTransLRBase :
        (insertEntryEquiv r r (1 : Kˣ) (ofGL (leftRec : GL (DeletedIndex m r) K))).trans
          (insertEntryEquiv r c a0 monoRec) =
          insertEntryEquiv r c ((1 : Kˣ) * a0)
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) :=
      insertEntryEquiv_trans r r c (1 : Kˣ) a0
        (ofGL (leftRec : GL (DeletedIndex m r) K)) monoRec
    have hTransLR : (insertEntryEquiv r r (1 : Kˣ)
          (ofGL (leftRec : GL (DeletedIndex m r) K))).trans monoIns =
          insertEntryEquiv r c a0
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) := by
      calc (insertEntryEquiv r r (1 : Kˣ)
            (ofGL (leftRec : GL (DeletedIndex m r) K))).trans monoIns
          = (insertEntryEquiv r r (1 : Kˣ)
              (ofGL (leftRec : GL (DeletedIndex m r) K))).trans
              (insertEntryEquiv r c a0 monoRec) := by rw [hMonoEqIns]
        _ = insertEntryEquiv r c ((1 : Kˣ) * a0)
              ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) :=
              hTransLRBase
        _ = insertEntryEquiv r c a0
              ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) := by
              rw [one_mul]
    have hTransRBase :
        (insertEntryEquiv r c a0 monoRec).trans
          (insertEntryEquiv c c (1 : Kˣ)
            (ofGL (rightRec : GL (DeletedIndex n c) K))) =
          insertEntryEquiv r c (a0 * 1)
            (monoRec.trans (ofGL (rightRec : GL (DeletedIndex n c) K))) :=
      insertEntryEquiv_trans r c c a0 (1 : Kˣ) monoRec
        (ofGL (rightRec : GL (DeletedIndex n c) K))
    have hTransR : monoIns.trans
          (insertEntryEquiv c c (1 : Kˣ)
            (ofGL (rightRec : GL (DeletedIndex n c) K))) =
          insertEntryEquiv r c a0
            (monoRec.trans (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
      calc monoIns.trans
            (insertEntryEquiv c c (1 : Kˣ)
              (ofGL (rightRec : GL (DeletedIndex n c) K)))
          = (insertEntryEquiv r c a0 monoRec).trans
              (insertEntryEquiv c c (1 : Kˣ)
                (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
              rw [hMonoEqIns]
        _ = insertEntryEquiv r c (a0 * 1)
              (monoRec.trans (ofGL (rightRec : GL (DeletedIndex n c) K))) :=
              hTransRBase
        _ = insertEntryEquiv r c a0
              (monoRec.trans (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
              rw [mul_one]
    have hTransMidBase :
        (insertEntryEquiv r c a0
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
          (insertEntryEquiv c c (1 : Kˣ)
            (ofGL (rightRec : GL (DeletedIndex n c) K))) =
          insertEntryEquiv r c (a0 * 1)
            (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
              (ofGL (rightRec : GL (DeletedIndex n c) K))) :=
      insertEntryEquiv_trans r c c a0 (1 : Kˣ)
        ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)
        (ofGL (rightRec : GL (DeletedIndex n c) K))
    have hTransMid :
        (insertEntryEquiv r c a0
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
          (insertEntryEquiv c c (1 : Kˣ)
            (ofGL (rightRec : GL (DeletedIndex n c) K))) =
          insertEntryEquiv r c a0
            (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
              (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
      calc (insertEntryEquiv r c a0
              ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
            (insertEntryEquiv c c (1 : Kˣ)
              (ofGL (rightRec : GL (DeletedIndex n c) K)))
          = insertEntryEquiv r c (a0 * 1)
              (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
                (ofGL (rightRec : GL (DeletedIndex n c) K))) := hTransMidBase
        _ = insertEntryEquiv r c a0
              (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
                (ofGL (rightRec : GL (DeletedIndex n c) K))) := by rw [mul_one]
    have hE0Eq : E0 =
          ((ofGL (leftEmb : GL m K)).trans monoIns).trans
            (ofGL (rightEmb : GL n K)) := by
      have h1 : E0 = insertEntryEquiv r c a0 eRed := hRecon.symm
      have h2 : eRed =
          ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
            (ofGL (rightRec : GL (DeletedIndex n c) K)) := by
        calc eRed = ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans
                (monomialEquiv uRec σRec)).trans
                (ofGL (rightRec : GL (DeletedIndex n c) K)) := hRedFac
          _ = ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
                (ofGL (rightRec : GL (DeletedIndex n c) K)) := rfl
      have h3 : insertEntryEquiv r c a0 eRed =
          insertEntryEquiv r c a0
            (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
              (ofGL (rightRec : GL (DeletedIndex n c) K))) := by rw [h2]
      have h4 : (ofGL (leftEmb : GL m K)).trans monoIns =
          insertEntryEquiv r c a0
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) := by
        calc (ofGL (leftEmb : GL m K)).trans monoIns
            = (insertEntryEquiv r r (1 : Kˣ)
                (ofGL (leftRec : GL (DeletedIndex m r) K))).trans monoIns := by
                rw [hLeftEmbInsert]
          _ = insertEntryEquiv r c a0
                ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec) :=
                hTransLR
      have h5 : ((ofGL (leftEmb : GL m K)).trans monoIns).trans
            (ofGL (rightEmb : GL n K)) =
          (insertEntryEquiv r c a0
            ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
            (insertEntryEquiv c c (1 : Kˣ)
              (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
        calc ((ofGL (leftEmb : GL m K)).trans monoIns).trans
              (ofGL (rightEmb : GL n K))
            = (insertEntryEquiv r c a0
                ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
                (ofGL (rightEmb : GL n K)) := by rw [h4]
          _ = (insertEntryEquiv r c a0
                ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
                (insertEntryEquiv c c (1 : Kˣ)
                  (ofGL (rightRec : GL (DeletedIndex n c) K))) := by
                rw [hRightEmbInsert]
      calc E0 = insertEntryEquiv r c a0 eRed := h1
        _ = insertEntryEquiv r c a0
              (((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec).trans
                (ofGL (rightRec : GL (DeletedIndex n c) K))) := h3
        _ = (insertEntryEquiv r c a0
              ((ofGL (leftRec : GL (DeletedIndex m r) K)).trans monoRec)).trans
              (insertEntryEquiv c c (1 : Kˣ)
                (ofGL (rightRec : GL (DeletedIndex n c) K))) := hTransMid.symm
        _ = ((ofGL (leftEmb : GL m K)).trans monoIns).trans
              (ofGL (rightEmb : GL n K)) := h5.symm
    let leftTotal : upperElementarySubgroup m K := leftClear⁻¹ * leftEmb
    let rightTotal : upperElementarySubgroup n K := rightEmb * rightClear⁻¹
    have hOfGLLeft : (ofGL (rowClear e.val r c hp)).symm =
        ofGL (leftClear⁻¹ : upperElementarySubgroup m K).val := by
      have : (leftClear⁻¹ : upperElementarySubgroup m K).val =
          (rowClear e.val r c hp)⁻¹ := by simp [leftClear]
      rw [this]
      rfl
    have hOfGLRight : (ofGL (columnClear e.val r c hp)).symm =
        ofGL (rightClear⁻¹ : upperElementarySubgroup n K).val := by
      have : (rightClear⁻¹ : upperElementarySubgroup n K).val =
          (columnClear e.val r c hp)⁻¹ := by simp [rightClear]
      rw [this]
      rfl
    have hFinal : e =
        ((ofGL (leftTotal : GL m K)).trans monoIns).trans
          (ofGL (rightTotal : GL n K)) := by
      have hCanon : E0 =
          ((ofGL (leftEmb : GL m K)).trans monoIns).trans
            (ofGL (rightEmb : GL n K)) := hE0Eq
      have hStep1 : e =
          ((ofGL (rowClear e.val r c hp)).symm.trans E0).trans
            (ofGL (columnClear e.val r c hp)).symm := hFact
      have hStep2 : (ofGL (rowClear e.val r c hp)).symm.trans E0 =
          (ofGL (rowClear e.val r c hp)).symm.trans
            (((ofGL (leftEmb : GL m K)).trans monoIns).trans
              (ofGL (rightEmb : GL n K))) := by rw [hCanon]
      have hStep3 : ((ofGL (rowClear e.val r c hp)).symm.trans
            (((ofGL (leftEmb : GL m K)).trans monoIns).trans
                (ofGL (rightEmb : GL n K)))).trans
            (ofGL (columnClear e.val r c hp)).symm =
          (((ofGL (rowClear e.val r c hp)).symm.trans
            (ofGL (leftEmb : GL m K))).trans monoIns).trans
            ((ofGL (rightEmb : GL n K)).trans
              (ofGL (columnClear e.val r c hp)).symm) := by
        calc ((ofGL (rowClear e.val r c hp)).symm.trans
              (((ofGL (leftEmb : GL m K)).trans monoIns).trans
                (ofGL (rightEmb : GL n K)))).trans
              (ofGL (columnClear e.val r c hp)).symm
            = ((((ofGL (rowClear e.val r c hp)).symm.trans
                ((ofGL (leftEmb : GL m K)).trans monoIns)).trans
                (ofGL (rightEmb : GL n K)))).trans
                (ofGL (columnClear e.val r c hp)).symm := by
                rw [← trans_assoc]
          _ = (((((ofGL (rowClear e.val r c hp)).symm.trans
                (ofGL (leftEmb : GL m K))).trans monoIns).trans
                (ofGL (rightEmb : GL n K)))).trans
                (ofGL (columnClear e.val r c hp)).symm := by
                rw [← trans_assoc]
          _ = (((ofGL (rowClear e.val r c hp)).symm.trans
                (ofGL (leftEmb : GL m K))).trans monoIns).trans
                ((ofGL (rightEmb : GL n K)).trans
                  (ofGL (columnClear e.val r c hp)).symm) := by
              rw [trans_assoc, trans_assoc]
      have hL : (ofGL (rowClear e.val r c hp)).symm.trans
            (ofGL (leftEmb : GL m K)) = ofGL (leftTotal : GL m K) := by
        rw [hOfGLLeft]
        apply ext
        simp [leftTotal, ofGL]
      have hR : (ofGL (rightEmb : GL n K)).trans
            (ofGL (columnClear e.val r c hp)).symm =
            ofGL (rightTotal : GL n K) := by
        rw [hOfGLRight]
        apply ext
        simp [rightTotal, ofGL]
      calc e = ((ofGL (rowClear e.val r c hp)).symm.trans E0).trans
              (ofGL (columnClear e.val r c hp)).symm := hStep1
        _ = ((ofGL (rowClear e.val r c hp)).symm.trans
              (((ofGL (leftEmb : GL m K)).trans monoIns).trans
                (ofGL (rightEmb : GL n K)))).trans
              (ofGL (columnClear e.val r c hp)).symm := by rw [hStep2]
        _ = (((ofGL (rowClear e.val r c hp)).symm.trans
              (ofGL (leftEmb : GL m K))).trans monoIns).trans
              ((ofGL (rightEmb : GL n K)).trans
                (ofGL (columnClear e.val r c hp)).symm) := hStep3
        _ = ((ofGL (leftTotal : GL m K)).trans monoIns).trans
              (ofGL (rightTotal : GL n K)) := by rw [hL, hR]
    { left := leftTotal
      weights := insertWeights r a0 uRec
      perm := insertEquiv r c σRec
      right := rightTotal
      factorization := hFinal }

/-- Every heterogeneous invertible matrix has a Bruhat decomposition. -/
theorem nonempty_heterogeneousBruhatDecomposition
    (e : GeneralLinearEquiv m n K) :
    Nonempty (HeterogeneousBruhatDecomposition e) :=
  ⟨heterogeneousBruhatDecompositionAux (Fintype.card m) e rfl⟩

/-- Canonical choice of the heterogeneous Bruhat decomposition. -/
noncomputable def heterogeneousBruhatDecomposition
    (e : GeneralLinearEquiv m n K) : HeterogeneousBruhatDecomposition e :=
  heterogeneousBruhatDecompositionAux (Fintype.card m) e rfl

/-- Clean existence statement for the heterogeneous Bruhat decomposition. -/
theorem exists_heterogeneousBruhatDecomposition
    (e : GeneralLinearEquiv m n K) :
    ∃ (left : upperElementarySubgroup m K) (weights : m → Kˣ) (perm : n ≃ m)
      (right : upperElementarySubgroup n K),
      e = ((ofGL (left : GL m K)).trans (monomialEquiv weights perm)).trans
            (ofGL (right : GL n K)) := by
  let d := heterogeneousBruhatDecomposition e
  exact ⟨d.left, d.weights, d.perm, d.right, d.factorization⟩

/-- Value-level existence: `e.val = L.val * monomial.val * R.val`. -/
theorem exists_heterogeneousBruhatDecomposition_val
    (e : GeneralLinearEquiv m n K) :
    ∃ (left : upperElementarySubgroup m K) (weights : m → Kˣ) (perm : n ≃ m)
      (right : upperElementarySubgroup n K),
      e.val =
        (left : GL m K).val * (monomialEquiv weights perm).val *
          (right : GL n K).val := by
  obtain ⟨l, w, p, r, h⟩ := exists_heterogeneousBruhatDecomposition e
  exact ⟨l, w, p, r, by
    have hV := congrArg GeneralLinearEquiv.val h
    simp only [val_trans] at hV
    exact hV⟩

private theorem HeterogeneousBruhatDecomposition_ext
    {e : GeneralLinearEquiv m n K}
    {d₁ d₂ : HeterogeneousBruhatDecomposition e}
    (hLeft : d₁.left = d₂.left)
    (hWeights : d₁.weights = d₂.weights)
    (hPerm : d₁.perm = d₂.perm)
    (hRight : d₁.right = d₂.right) : d₁ = d₂ := by
  cases d₁ with | mk l1 w1 p1 r1 f1 =>
  cases d₂ with | mk l2 w2 p2 r2 f2 =>
  simp only at hLeft hWeights hPerm hRight
  subst hLeft
  subst hWeights
  subst hPerm
  subst hRight
  have : f1 = f2 := Subsingleton.elim _ _
  subst this
  rfl

private theorem emptyBruhatDecomposition_map_eq
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n]
    {K L : Type*} [DivisionRing K] [DivisionRing L]
    [IsEmpty m] [IsEmpty n]
    (e : GeneralLinearEquiv m n K) (f : K →+* L) :
    (emptyBruhatDecomposition (K := K) e).map f =
      emptyBruhatDecomposition (e.map f) := by
  apply HeterogeneousBruhatDecomposition_ext
  · simp only [HeterogeneousBruhatDecomposition.map, emptyBruhatDecomposition]
    exact (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f).map_one
  · funext i
    exact isEmptyElim i
  · rfl
  · simp only [HeterogeneousBruhatDecomposition.map, emptyBruhatDecomposition]
    exact (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f).map_one

private theorem emptyDecompositionOfCardZero_map_eq
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n]
    {K L : Type*} [DivisionRing K] [DivisionRing L]
    (e : GeneralLinearEquiv m n K) (h0 : Fintype.card m = 0) (f : K →+* L) :
    (emptyDecompositionOfCardZero e h0).map f =
      emptyDecompositionOfCardZero (e.map f) h0 := by
  apply HeterogeneousBruhatDecomposition_ext
  · simp only [HeterogeneousBruhatDecomposition.map, emptyDecompositionOfCardZero,
      emptyBruhatDecomposition]
    exact (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f).map_one
  · funext i
    have : IsEmpty m := by rwa [Fintype.card_eq_zero_iff] at h0
    exact isEmptyElim i
  · rfl
  · simp only [HeterogeneousBruhatDecomposition.map, emptyDecompositionOfCardZero,
      emptyBruhatDecomposition]
    exact (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom f).map_one

private theorem reducedPivotEquiv_cast_eq_reindex {m n : Type*} [DecidableEq m] [DecidableEq n]
    [Fintype m] [Fintype n] {R : Type*} [DivisionRing R]
    {r₁ r₂ : m} (h : r₁ = r₂) (c : n)
    (e : GeneralLinearEquiv (DeletedIndex m r₁) (DeletedIndex n c) R) :
    (h ▸ e : GeneralLinearEquiv (DeletedIndex m r₂) (DeletedIndex n c) R) =
      e.reindex (deletedIndexEquivOfEq h.symm) (Equiv.refl _) := by
  cases h
  apply GeneralLinearEquiv.ext
  ext i j
  simp only [GeneralLinearEquiv.val_reindex, Matrix.submatrix_apply]
  have hI : (deletedIndexEquivOfEq (rfl : r₁ = r₁)) i = i := by
    apply Subtype.ext
    rfl
  simp [hI]

private theorem reducedPivotEquiv_map_eq
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n]
    {K L : Type*} [DivisionRing K] [DivisionRing L]
    (e : GeneralLinearEquiv m n K) (f : K →+* L) [Nonempty n] :
    (reducedPivotEquiv e).map f =
      (show canonicalPivotRow (e.map f) = canonicalPivotRow e from by
        change pivotRow (e.map f) (canonicalColumn : n) =
            pivotRow e (canonicalColumn : n)
        exact canonicalPivotRow_map e f) ▸
        (reducedPivotEquiv (e.map f)) := by
  have hReindex := reducedPivotEquiv_map_eq_reindex (e := e) (f := f)
  have hCastReindex :=
    reducedPivotEquiv_cast_eq_reindex (canonicalPivotRow_map e f) (canonicalColumn : n)
      (reducedPivotEquiv (e.map f))
  exact hReindex.trans hCastReindex.symm

private theorem heterogeneousBruhatDecompositionAux_build_map
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] {K L : Type*} [DivisionRing K] [DivisionRing L]
    (e : GeneralLinearEquiv m n K) (f : K →+* L) [Nonempty n]
    (recDec : HeterogeneousBruhatDecomposition
      (reducedPivotEquiv e))
    (recDecMap : HeterogeneousBruhatDecomposition
      (reducedPivotEquiv (e.map f)))
    (hRec : HEq recDecMap (recDec.map f)) :
    (heterogeneousBruhatDecompositionAux_build e recDec).map f =
      heterogeneousBruhatDecompositionAux_build (e.map f) recDecMap := by
  have hRow : canonicalPivotRow (e.map f) = canonicalPivotRow e := by
    change pivotRow (e.map f) (canonicalColumn : n) = pivotRow e (canonicalColumn : n)
    exact canonicalPivotRow_map e f
  have hp : e.val (canonicalPivotRow e) (canonicalColumn : n) ≠ 0 :=
    @canonicalPivotRow_ne_zero m n _ _ _ _ _ _ ‹Nonempty n› K _ e
  have hp' : (e.map f).val (canonicalPivotRow (e.map f)) (canonicalColumn : n) ≠ 0 :=
    hRow.symm ▸ divRingHom_map_ne_zero f hp
  have hpEq : divRingHom_map_ne_zero f hp = hRow ▸ hp' := Subsingleton.elim _ _
  have hLeftClearMap :
      Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := m) f
        (leftUpperFactor e (canonicalPivotRow e) (canonicalColumn : n) hp) =
        leftUpperFactor (e.map f) (canonicalPivotRow (e.map f))
          (canonicalColumn : n) hp' := by
    simp only [leftUpperFactor]
    have hBase : Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := m) f
        (upperRowClear e.val (canonicalPivotRow e) (canonicalColumn : n) hp) =
        upperRowClear (e.map f).val (canonicalPivotRow e) (canonicalColumn : n)
          (divRingHom_map_ne_zero f hp) :=
      upperRowClear_map e.val (canonicalPivotRow e) (canonicalColumn : n) hp f _
    rw [hpEq] at hBase
    refine hBase.trans ?_
    have aux : ∀ (rMap r : m) (h : rMap = r)
        (hpMap : (e.map f).val rMap (canonicalColumn : n) ≠ 0),
        upperRowClear (e.map f).val r (canonicalColumn : n) (h ▸ hpMap) =
          upperRowClear (e.map f).val rMap (canonicalColumn : n) hpMap :=
      fun _ _ h _ => by cases h; rfl
    exact aux _ _ hRow hp'
  have hRightClearMap :
      Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := n) f
        (rightUpperFactor e (canonicalPivotRow e) (canonicalColumn : n) hp) =
        rightUpperFactor (e.map f) (canonicalPivotRow (e.map f))
          (canonicalColumn : n) hp' := by
    simp only [rightUpperFactor]
    have hBase : Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := n) f
        (upperColumnClear e.val (canonicalPivotRow e) (canonicalColumn : n) hp) =
        upperColumnClear (e.map f).val (canonicalPivotRow e) (canonicalColumn : n)
          (divRingHom_map_ne_zero f hp) :=
      upperColumnClear_map e.val (canonicalPivotRow e) (canonicalColumn : n) hp f _
    rw [hpEq] at hBase
    refine hBase.trans ?_
    have aux : ∀ (rMap r : m) (h : rMap = r)
        (hpMap : (e.map f).val rMap (canonicalColumn : n) ≠ 0),
        upperColumnClear (e.map f).val r (canonicalColumn : n) (h ▸ hpMap) =
          upperColumnClear (e.map f).val rMap (canonicalColumn : n) hpMap :=
      fun _ _ h _ => by cases h; rfl
    exact aux _ _ hRow hp'
  have hCompRow := upper_extendByIdentity_mapRingHom
    (e := Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e)) (f := f)
  have hCompCol := upper_extendByIdentity_mapRingHom
    (e := Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n)) (f := f)
  have hEmbEq : Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e) =
      hRow ▸ Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow (e.map f)) := by
    have aux : ∀ (rMap r : m) (h : rMap = r),
        Matrix.GeneralLinearGroup.deletedOrderEmbedding r =
          h ▸ Matrix.GeneralLinearGroup.deletedOrderEmbedding rMap :=
      fun _ _ h => by cases h; rfl
    exact aux (canonicalPivotRow (e.map f)) (canonicalPivotRow e) hRow
  apply HeterogeneousBruhatDecomposition_ext
  · simp only [HeterogeneousBruhatDecomposition.map, heterogeneousBruhatDecompositionAux_build]
    have hRedEq : (reducedPivotEquiv e).map f =
        hRow ▸ reducedPivotEquiv (e.map f) :=
      reducedPivotEquiv_map_eq (e := e) (f := f)
    have hLeftEmb :
        Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := m) f
          (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e))
            recDec.left) =
          Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e))
            (recDec.map f).left := by
      calc _ = (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
              (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e)))
            ((Matrix.GeneralLinearGroup.UpperElementary.mapRingHom
                (ι := DeletedIndex m (canonicalPivotRow e)) f) recDec.left) :=
            DFunLike.congr_fun hCompRow recDec.left
        _ = _ := rfl
    have hLeftHEq : HEq recDecMap.left (recDec.map f).left := by
      have aux : ∀ (rMap r : m) (h : rMap = r)
          (eMap : GeneralLinearEquiv (DeletedIndex m rMap)
            (DeletedIndex n canonicalColumn) L)
          (eOrig : GeneralLinearEquiv (DeletedIndex m r)
            (DeletedIndex n canonicalColumn) L)
          (hEq : eOrig = h ▸ eMap)
          (dMap : HeterogeneousBruhatDecomposition eMap)
          (d : HeterogeneousBruhatDecomposition eOrig)
          (hRec : HEq dMap d),
          HEq dMap.left d.left := by
        intro rMap r h eMap eOrig hEq dMap d hRec
        cases h
        cases hEq
        cases hRec
        rfl
      exact aux (canonicalPivotRow (e.map f)) (canonicalPivotRow e) hRow
        (reducedPivotEquiv (e.map f)) ((reducedPivotEquiv e).map f) hRedEq
        recDecMap (recDec.map f) hRec
    have hLeftEmb' :
        Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e))
            (recDec.map f).left =
          Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding
              (canonicalPivotRow (e.map f))) recDecMap.left := by
      have aux2 : ∀ (rMap r : m) (h : rMap = r)
          (l' : Matrix.GeneralLinearGroup.upperElementarySubgroup
            (DeletedIndex m rMap) L)
          (l : Matrix.GeneralLinearGroup.upperElementarySubgroup
            (DeletedIndex m r) L)
          (hHEq : HEq l' l),
          Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
              (Matrix.GeneralLinearGroup.deletedOrderEmbedding r) l =
            Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
              (Matrix.GeneralLinearGroup.deletedOrderEmbedding rMap) l' := by
        intro rMap r h l' l hHEq
        cases h
        cases hHEq
        rfl
      exact aux2 (canonicalPivotRow (e.map f)) (canonicalPivotRow e)
        hRow recDecMap.left (recDec.map f).left hLeftHEq
    calc (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := m) f
            ((leftUpperFactor e (canonicalPivotRow e) (canonicalColumn : n) hp)⁻¹ *
              Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
                (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e))
                recDec.left))
        = ((Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := m) f
            (leftUpperFactor e (canonicalPivotRow e) (canonicalColumn : n) hp))⁻¹ *
          Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := m) f
            (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
              (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e))
              recDec.left)) := by simp [map_mul, map_inv]
      _ = ((leftUpperFactor (e.map f) (canonicalPivotRow (e.map f)) (canonicalColumn : n) hp')⁻¹ *
          Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow e))
            (recDec.map f).left) := by rw [hLeftClearMap, hLeftEmb]
      _ = ((leftUpperFactor (e.map f) (canonicalPivotRow (e.map f)) (canonicalColumn : n) hp')⁻¹ *
          Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalPivotRow (e.map f)))
            recDecMap.left) := by rw [hLeftEmb']
  · simp only [HeterogeneousBruhatDecomposition.map,
      heterogeneousBruhatDecompositionAux_build]
    have hUnit : Units.map (f : K →+* L).toMonoidHom
        (canonicalPivotUnit e) =
        canonicalPivotUnit (e.map f) :=
      canonicalPivotUnit_map (e := e) (f := f)
    have hRedEq : (reducedPivotEquiv e).map f =
        hRow ▸ reducedPivotEquiv (e.map f) :=
      reducedPivotEquiv_map_eq (e := e) (f := f)
    funext i
    by_cases hi : i = canonicalPivotRow e
    · have hi' : i = canonicalPivotRow (e.map f) :=
        hi.trans hRow.symm
      have hL : Units.map (f : K →+* L).toMonoidHom
            (insertWeights (canonicalPivotRow e)
              (canonicalPivotUnit e) recDec.weights i) =
          Units.map (f : K →+* L).toMonoidHom
            (canonicalPivotUnit e) := by
        rw [hi, insertWeights_apply_self]
      have hR : insertWeights (canonicalPivotRow (e.map f))
            (canonicalPivotUnit (e.map f)) recDecMap.weights i =
          canonicalPivotUnit (e.map f) := by
        rw [hi', insertWeights_apply_self]
      exact (hL.trans (hUnit.trans hR.symm))
    · have hi' : i ≠ canonicalPivotRow (e.map f) := by
        intro hEq
        exact hi (hEq.trans hRow)
      have hL : Units.map (f : K →+* L).toMonoidHom
            (insertWeights (canonicalPivotRow e)
              (canonicalPivotUnit e) recDec.weights i) =
          Units.map (f : K →+* L).toMonoidHom
            (recDec.weights ⟨i, hi⟩) := by
        rw [insertWeights_apply_of_ne hi]
      have hR : insertWeights (canonicalPivotRow (e.map f))
            (canonicalPivotUnit (e.map f))
            recDecMap.weights i =
          recDecMap.weights ⟨i, hi'⟩ := by
        rw [insertWeights_apply_of_ne hi']
      have hMid : Units.map (f : K →+* L).toMonoidHom
            (recDec.weights ⟨i, hi⟩) =
          recDecMap.weights ⟨i, hi'⟩ := by
        have hEq : recDecMap.weights ⟨i, hi'⟩ =
            (recDec.map f).weights ⟨i, hi⟩ := by
          have aux : ∀ (rMap r : m) (h : rMap = r)
              (eMap : GeneralLinearEquiv
                (DeletedIndex m rMap)
                (DeletedIndex n canonicalColumn) L)
              (eOrig : GeneralLinearEquiv
                (DeletedIndex m r)
                (DeletedIndex n canonicalColumn) L)
              (hEq : eOrig = h ▸ eMap)
              (dMap : HeterogeneousBruhatDecomposition eMap)
              (d : HeterogeneousBruhatDecomposition eOrig)
              (hRec : HEq dMap d) (i : m)
              (hiMap : i ≠ rMap) (hiOrig : i ≠ r),
              dMap.weights ⟨i, hiMap⟩ =
                d.weights ⟨i, hiOrig⟩ := by
            intro rMap r h eMap eOrig hEq dMap d hRec i hiMap hiOrig
            cases h
            cases hEq
            cases hRec
            exact congrArg dMap.weights (Subtype.ext rfl)
          exact aux (canonicalPivotRow (e.map f))
            (canonicalPivotRow e) hRow
            (reducedPivotEquiv (e.map f))
            ((reducedPivotEquiv e).map f) hRedEq
            recDecMap (recDec.map f) hRec i hi' hi
        calc Units.map (f : K →+* L).toMonoidHom
                (recDec.weights ⟨i, hi⟩) =
              (recDec.map f).weights ⟨i, hi⟩ := rfl
          _ = recDecMap.weights ⟨i, hi'⟩ := hEq.symm
      exact (hL.trans (hMid.trans hR.symm))
  · simp only [HeterogeneousBruhatDecomposition.map, heterogeneousBruhatDecompositionAux_build]
    have hRedEq : (reducedPivotEquiv e).map f =
        hRow ▸ reducedPivotEquiv (e.map f) :=
      reducedPivotEquiv_map_eq (e := e) (f := f)
    have : insertEquiv (canonicalPivotRow e) (canonicalColumn : n)
        recDec.perm =
        insertEquiv (canonicalPivotRow (e.map f)) (canonicalColumn : n)
          recDecMap.perm := by
      have aux : ∀ (rMap r : m) (h : rMap = r)
          (eMap : GeneralLinearEquiv (DeletedIndex m rMap)
            (DeletedIndex n canonicalColumn) L)
          (eOrig : GeneralLinearEquiv (DeletedIndex m r)
            (DeletedIndex n canonicalColumn) L)
          (hEq : eOrig = h ▸ eMap)
          (dMap : HeterogeneousBruhatDecomposition eMap)
          (d : HeterogeneousBruhatDecomposition eOrig)
          (hRec : HEq dMap d),
          insertEquiv r (canonicalColumn : n) d.perm =
            insertEquiv rMap (canonicalColumn : n) dMap.perm := by
        intro rMap r h eMap eOrig hEq dMap d hRec
        cases h
        cases hEq
        cases hRec
        rfl
      exact aux (canonicalPivotRow (e.map f)) (canonicalPivotRow e) hRow
        (reducedPivotEquiv (e.map f)) ((reducedPivotEquiv e).map f)
        hRedEq recDecMap (recDec.map f) hRec
    exact this
  · simp only [HeterogeneousBruhatDecomposition.map, heterogeneousBruhatDecompositionAux_build]
    have hRightEmb :
        Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := n) f
          (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n)) recDec.right) =
          Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n))
            (recDec.map f).right := by
      calc _ = (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
              (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n)))
            ((Matrix.GeneralLinearGroup.UpperElementary.mapRingHom
                (ι := DeletedIndex n (canonicalColumn : n)) f) recDec.right) :=
            DFunLike.congr_fun hCompCol recDec.right
        _ = _ := rfl
    have hRedEq : (reducedPivotEquiv e).map f =
        hRow ▸ reducedPivotEquiv (e.map f) :=
      reducedPivotEquiv_map_eq (e := e) (f := f)
    have hRightEq : (recDec.map f).right = recDecMap.right := by
      have aux : ∀ (rMap r : m) (h : rMap = r)
          (eMap : GeneralLinearEquiv (DeletedIndex m rMap)
            (DeletedIndex n canonicalColumn) L)
          (eOrig : GeneralLinearEquiv (DeletedIndex m r)
            (DeletedIndex n canonicalColumn) L)
          (hEq : eOrig = h ▸ eMap)
          (dMap : HeterogeneousBruhatDecomposition eMap)
          (d : HeterogeneousBruhatDecomposition eOrig)
          (hRec : HEq dMap d),
          d.right = dMap.right := by
        intro rMap r h eMap eOrig hEq dMap d hRec
        cases h
        cases hEq
        cases hRec
        rfl
      exact aux (canonicalPivotRow (e.map f)) (canonicalPivotRow e) hRow
        (reducedPivotEquiv (e.map f)) ((reducedPivotEquiv e).map f) hRedEq
        recDecMap (recDec.map f) hRec
    calc (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := n) f
            (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
                (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n))
                recDec.right *
              (rightUpperFactor e (canonicalPivotRow e) (canonicalColumn : n) hp)⁻¹))
        = (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := n) f
            (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
              (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n))
              recDec.right) *
          (Matrix.GeneralLinearGroup.UpperElementary.mapRingHom (ι := n) f
            (rightUpperFactor e (canonicalPivotRow e) (canonicalColumn : n) hp))⁻¹) := by
          simp [map_mul, map_inv]
      _ = (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n))
            (recDec.map f).right *
          (rightUpperFactor (e.map f) (canonicalPivotRow (e.map f))
            (canonicalColumn : n) hp')⁻¹) := by
          rw [hRightEmb, hRightClearMap]
      _ = (Matrix.GeneralLinearGroup.UpperElementary.extendByIdentity
            (Matrix.GeneralLinearGroup.deletedOrderEmbedding (canonicalColumn : n))
            recDecMap.right *
          (rightUpperFactor (e.map f) (canonicalPivotRow (e.map f))
            (canonicalColumn : n) hp')⁻¹) := by
          rw [hRightEq]

private theorem heterogeneousBruhatDecompositionAux_map (k : Nat)
    {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
    [LinearOrder m] [LinearOrder n] {K L : Type*} [DivisionRing K] [DivisionRing L]
    (e : GeneralLinearEquiv m n K) (hCard : Fintype.card m = k) (f : K →+* L) :
    (heterogeneousBruhatDecompositionAux k e hCard).map f =
      heterogeneousBruhatDecompositionAux k (e.map f) hCard := by
  induction k generalizing m n with
  | zero =>
    calc (heterogeneousBruhatDecompositionAux 0 e hCard).map f
        = (emptyDecompositionOfCardZero e hCard).map f := rfl
      _ = emptyDecompositionOfCardZero (e.map f) hCard :=
          emptyDecompositionOfCardZero_map_eq e hCard f
      _ = heterogeneousBruhatDecompositionAux 0 (e.map f) hCard := rfl
  | succ k ih =>
    have hCardPos : 0 < Fintype.card m := by omega
    have hNonemptyM : Nonempty m := by
      have hEquiv : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
      have hFin : Nonempty (Fin (Fintype.card m)) := ⟨⟨0, hCardPos⟩⟩
      exact ⟨hEquiv.symm hFin.some⟩
    have hNonemptyN : Nonempty n := by
      have : Nonempty m := hNonemptyM
      exact nonempty_n_of_nonempty_m e
    have : Nonempty m := hNonemptyM
    have : Nonempty n := hNonemptyN
    let c : n := @canonicalColumn n _ _ ‹Nonempty n›
    let r : m := @canonicalPivotRow m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    have hp : e.val r c ≠ 0 :=
      @canonicalPivotRow_ne_zero m n _ _ _ _ _ _ ‹Nonempty n› K _ e
    let eRed : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) K :=
      reducedPivotEquiv e
    have hDel : Fintype.card (DeletedIndex m r) = k := by
      have h := Matrix.GeneralLinearGroup.card_DeletedIndex (ι := m) r
      omega
    have hRow : canonicalPivotRow (e.map f) = r := by
      change pivotRow (e.map f) (canonicalColumn : n) =
          pivotRow e (canonicalColumn : n)
      exact (canonicalPivotRow_map (e := e) (f := f)).trans rfl
    let eRedMap : GeneralLinearEquiv
        (DeletedIndex m (canonicalPivotRow (e.map f)))
        (DeletedIndex n c) L :=
      reducedPivotEquiv (e.map f)
    have hDelMap : Fintype.card
        (DeletedIndex m (canonicalPivotRow (e.map f))) = k := by
      have h := Matrix.GeneralLinearGroup.card_DeletedIndex
        (ι := m) (canonicalPivotRow (e.map f))
      omega
    have hRedMap : eRed.map f = hRow ▸ eRedMap := by
      exact reducedPivotEquiv_map_eq (e := e) (f := f)
    have ihRec : (heterogeneousBruhatDecompositionAux k eRed hDel).map f =
        heterogeneousBruhatDecompositionAux k (eRed.map f) hDel :=
      ih (m := DeletedIndex m r) (n := DeletedIndex n c) eRed hDel
    have hRecHEq : HEq
        (heterogeneousBruhatDecompositionAux k eRedMap hDelMap)
        ((heterogeneousBruhatDecompositionAux k eRed hDel).map f) := by
      have h1 : HEq
          (heterogeneousBruhatDecompositionAux k eRedMap hDelMap)
          (heterogeneousBruhatDecompositionAux k (eRed.map f) hDel) := by
        have aux : ∀ (rMap r : m) (h : rMap = r)
            (eMap : GeneralLinearEquiv (DeletedIndex m rMap)
              (DeletedIndex n c) L)
            (eCast : GeneralLinearEquiv (DeletedIndex m r)
              (DeletedIndex n c) L) (hEq : eCast = h ▸ eMap)
            (hDelMap : Fintype.card (DeletedIndex m rMap) = k)
            (hDel : Fintype.card (DeletedIndex m r) = k),
            HEq (heterogeneousBruhatDecompositionAux k eMap hDelMap)
              (heterogeneousBruhatDecompositionAux k eCast hDel) := by
          intro rMap r h eMap eCast hEq hDelMap hDel
          cases h
          cases hEq
          have hDelEq : hDelMap = hDel := Subsingleton.elim _ _
          cases hDelEq
          rfl
        exact aux (canonicalPivotRow (e.map f)) r hRow
          eRedMap (eRed.map f) hRedMap hDelMap hDel
      have h2 : HEq
          (heterogeneousBruhatDecompositionAux k (eRed.map f) hDel)
          ((heterogeneousBruhatDecompositionAux k eRed hDel).map f) := by
        rw [ihRec]
      exact h1.trans h2
    have hAuxLeft :
        heterogeneousBruhatDecompositionAux (Nat.succ k) e hCard =
          heterogeneousBruhatDecompositionAux_build e
            (heterogeneousBruhatDecompositionAux k eRed hDel) := rfl
    have hAuxRight :
        heterogeneousBruhatDecompositionAux (Nat.succ k) (e.map f) hCard =
          heterogeneousBruhatDecompositionAux_build (e.map f)
            (heterogeneousBruhatDecompositionAux k eRedMap hDelMap) := rfl
    calc (heterogeneousBruhatDecompositionAux (Nat.succ k) e hCard).map f
        = (heterogeneousBruhatDecompositionAux_build e
            (heterogeneousBruhatDecompositionAux k eRed hDel)).map f := by
            rw [hAuxLeft]
      _ = heterogeneousBruhatDecompositionAux_build (e.map f)
            (heterogeneousBruhatDecompositionAux k eRedMap hDelMap) := by
            exact heterogeneousBruhatDecompositionAux_build_map (e := e)
              (f := f)
              (recDec := heterogeneousBruhatDecompositionAux k eRed hDel)
              (recDecMap :=
                heterogeneousBruhatDecompositionAux k eRedMap hDelMap)
              (hRec := hRecHEq)
      _ = heterogeneousBruhatDecompositionAux (Nat.succ k) (e.map f) hCard := by
            rw [hAuxRight]

end Inductive

section Map

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

/-- Coefficient naturality for the canonical heterogeneous Bruhat decomposition
over division rings. The canonical decomposition commutes with any division-ring
homomorphism `f : K →+* L` on all four components: left upper factor, unit
weights, permutation and right upper factor. The proof is by structural induction
on `Fintype.card m`, using the reusable private nonzero-branch equation
`heterogeneousBruhatDecompositionAux_build`, together with
`leftUpperFactor`/`rightUpperFactor` naturality (`upperRowClear_map`,
`upperColumnClear_map`), `insertWeights`/`insertEquiv` preservation,
`UpperElementary.extendByIdentity` naturality (`upper_extendByIdentity_mapRingHom`),
and the pivot lemmas `canonicalPivotRow_map`, `canonicalPivotUnit_map`,
`reducedPivotEquiv_map_eq`. The empty case follows from `IsEmpty` elimination
for weights and `map_one` for the unipotent factors. -/
theorem heterogeneousBruhatDecomposition_map
    (e : GeneralLinearEquiv m n K) (f : K →+* L) :
    (heterogeneousBruhatDecomposition e).map f =
      heterogeneousBruhatDecomposition (e.map f) := by
  have hCard : Fintype.card m = Fintype.card m := rfl
  have h := heterogeneousBruhatDecompositionAux_map (Fintype.card m) e rfl f
  simp only [heterogeneousBruhatDecomposition] at h ⊢
  exact h

end Map

end GeneralLinearEquiv

end Matrix
