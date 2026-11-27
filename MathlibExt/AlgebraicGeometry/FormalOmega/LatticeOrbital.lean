/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_LatticeTreeOrbital.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeNeighbour
public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeGalois
import Mathlib.Tactic.LinearCombination

/-!
# Fixed vertices and orbital counts on the lattice graph

For `g ∈ GL₂(K)`, `LT.LatticeTree.fixedVertexSet g` is the set of vertices fixed by `g` and
`LT.LatticeTree.unitOrbitalCount R g` its cardinality (as `Nat.card`). Conjugating `g` by `h`
translates the fixed set by `h` and preserves its count, and scalars fix every vertex. Let `R` be a
domain with fraction field `K`, let `M ∈ GL₂(R)`, let `ϖ` be prime and not divide both `c` and `d`,
and write `(x, y) = M (c, d)ᵀ`. If the submodule `LT.LatticeTree.interLattice R K ϖ c d` is a full
lattice and `M` fixes its vertex, then `ϖ ∣ d x - c y` (`dvd_of_isFixedVertex_interLattice`). For
`λ ∈ Rˣ` with `(x, y) ≡ λ (c, d)` modulo `ϖ`, `M` maps that submodule onto itself. If `σ² = id`,
the vertices fixed by the twisted action of `(δ, σ)` are fixed by `normTwo δ σ`, and if `σ³ = id`,
by `normThree δ σ`; so the twisted count is `1` when that product has at most one fixed vertex and
some vertex is twisted-fixed.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace LT.LatticeTree

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

attribute [local simp] mem_stdLattice latticeMap_one IntegralAut.symm_toField
  IntegralAut.symm_toBase galVec_symm_galVec galVec_galVec_symm latticeGal_symm_latticeGal
  latticeGal_latticeGal_symm

/-- `v` is a fixed vertex of `g ∈ GL₂(K)`. -/
def IsFixedVertex (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) : Prop :=
  Vertex.act g v = v

/-- The set of vertices fixed by `g ∈ GL₂(K)`. -/
def fixedVertexSet (g : Matrix.GeneralLinearGroup (Fin 2) K) : Set (Vertex R K) :=
  {v | IsFixedVertex g v}

theorem mem_fixedVertexSet {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {v : Vertex R K} : v ∈ fixedVertexSet (R := R) g ↔ Vertex.act g v = v :=
  Iff.rfl

attribute [local simp] mem_fixedVertexSet
variable (R) in
/-- The number of vertices fixed by `g`, as a natural number (`0` if there are infinitely many). -/
noncomputable def unitOrbitalCount (g : Matrix.GeneralLinearGroup (Fin 2) K) : ℕ :=
  Nat.card (fixedVertexSet (R := R) g)

theorem isFixedVertex_mk_iff {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {hL : Submodule.IsFullLattice K L} :
    IsFixedVertex g (Vertex.mk R K L hL) ↔ Homothetic (latticeMap g L) L := by
  rw [IsFixedVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff]

theorem isFixedVertex_mk_of_latticeMap_eq {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {hL : Submodule.IsFullLattice K L}
    (h : latticeMap g L = L) : IsFixedVertex g (Vertex.mk R K L hL) :=
  isFixedVertex_mk_iff.mpr (by rw [h]; exact Homothetic.refl L)

theorem isFixedVertex_conj_iff (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (v : Vertex R K) :
    IsFixedVertex (h * g * h⁻¹) v ↔ IsFixedVertex g (Vertex.act h⁻¹ v) := by
  unfold IsFixedVertex
  rw [Vertex.act_mul, Vertex.act_mul]
  constructor
  · intro hfix
    have h2 := congrArg (Vertex.act h⁻¹) hfix
    rwa [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one] at h2
  · intro hfix
    rw [hfix, ← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

/-- The fixed vertices of a conjugate `h g h⁻¹` are the `h`-translates of those of `g`. -/
theorem fixedVertexSet_conj (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    fixedVertexSet (R := R) (h * g * h⁻¹) = Vertex.act h '' fixedVertexSet (R := R) g := by
  ext v
  constructor
  · intro hv
    exact ⟨Vertex.act h⁻¹ v, (isFixedVertex_conj_iff g h v).mp hv, by
      rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]⟩
  · rintro ⟨w, hw, rfl⟩
    refine (isFixedVertex_conj_iff g h _).mpr ?_
    show IsFixedVertex g (Vertex.act h⁻¹ (Vertex.act h w))
    rwa [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

/-- The fixed-vertex count is a conjugacy invariant. -/
theorem unitOrbitalCount_conj (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    unitOrbitalCount R (h * g * h⁻¹) = unitOrbitalCount R g := by
  rw [unitOrbitalCount, unitOrbitalCount, fixedVertexSet_conj]
  have hinj : Function.Injective (Vertex.act (R := R) h) := fun v w hvw => by
    have h2 := congrArg (Vertex.act h⁻¹) hvw
    rwa [← Vertex.act_mul, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one,
      Vertex.act_one] at h2
  exact Nat.card_congr (Equiv.Set.image _ _ hinj).symm

/-- Scalar matrices fix every vertex. -/
theorem isFixedVertex_scalarGL (c : Kˣ) (v : Vertex R K) :
    IsFixedVertex (scalarGL c) v := by
  induction v using Quotient.inductionOn with
  | h L =>
    obtain ⟨L, hL⟩ := L
    change Vertex.act (scalarGL c) (Vertex.mk R K L hL) = Vertex.mk R K L hL
    rw [Vertex.act_mk, Vertex.mk_eq_mk_iff]
    exact Homothetic.symm ⟨c, rfl⟩

theorem fixedVertexSet_scalarGL (c : Kˣ) :
    fixedVertexSet (R := R) (scalarGL c) = Set.univ :=
  Set.eq_univ_of_forall (isFixedVertex_scalarGL c)

/-- When `K` is the fraction field of `R` and `R` has an irreducible element, a scalar matrix fixes
more than one vertex. -/
theorem not_subsingleton_fixedVertexSet_scalarGL [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) (c : Kˣ) :
    ¬ (fixedVertexSet (R := R) (scalarGL c)).Subsingleton := by
  intro hsub
  exact stdVertex_ne_act_diagSnd (K := K) hϖ
    (hsub (isFixedVertex_scalarGL c _) (isFixedVertex_scalarGL c _)).symm

/-- When `K` is the fraction field of `R`, every matrix in `GL₂(R)` fixes the standard vertex. -/
theorem isFixedVertex_stdVertex_of_mem_range [IsFractionRing R K]
    {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    IsFixedVertex g (stdVertex R K) :=
  (Vertex.act_stdVertex_eq_iff g).mpr ⟨1, by rwa [scalarGL_one, one_mul]⟩

theorem nonempty_fixedVertexSet_of_mem_range [IsFractionRing R K]
    {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    (fixedVertexSet (R := R) g).Nonempty :=
  ⟨stdVertex R K, isFixedVertex_stdVertex_of_mem_range hg⟩

section Engine

variable [IsFractionRing R K]

/-- The product `M (c, d)ᵀ` of a matrix over `R` with a pair. -/
def mulVecPair (M : Matrix (Fin 2) (Fin 2) R) (c d : R) : Fin 2 → R :=
  M *ᵥ ![c, d]

@[simp] theorem mulVecPair_zero (M : Matrix (Fin 2) (Fin 2) R) (c d : R) :
    mulVecPair M c d 0 = M 0 0 * c + M 0 1 * d := by
  simp [mulVecPair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem mulVecPair_one (M : Matrix (Fin 2) (Fin 2) R) (c d : R) :
    mulVecPair M c d 1 = M 1 0 * c + M 1 1 * d := by
  simp [mulVecPair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVecPair_mul (M N : Matrix (Fin 2) (Fin 2) R) (c d : R) (i : Fin 2) :
    mulVecPair (M * N) c d i =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) i := by
  have h0 : mulVecPair (M * N) c d 0 =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) 0 := by
    simp only [mulVecPair_zero, mulVecPair_one, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h1 : mulVecPair (M * N) c d 1 =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) 1 := by
    simp only [mulVecPair_zero, mulVecPair_one, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  fin_cases i
  · exact h0
  · exact h1

omit [IsFractionRing R K] in
theorem latticeMap_map_interLattice_le (M : Matrix.GeneralLinearGroup (Fin 2) R)
    (ϖ c d : R) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) ≤
      interLattice R K ϖ (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
        (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) := by
  rintro _ ⟨w, hwmem, rfl⟩
  obtain ⟨hwint, t, ht, hweq⟩ := hwmem
  have hcoord : ∀ i : Fin 2,
      (mulVecLinR (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) M) w) i =
        algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) i 0) * w 0 +
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) i 1) * w 1 := by
    intro i
    rw [mulVecLinR_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  refine ⟨fun i => ?_, algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R).det) * t,
    IsLocalization.isInteger_mul ⟨_, rfl⟩ ht, ?_⟩
  · rw [hcoord i]
    exact IsLocalization.isInteger_add
      (IsLocalization.isInteger_mul ⟨_, rfl⟩ (hwint 0))
      (IsLocalization.isInteger_mul ⟨_, rfl⟩ (hwint 1))
  · rw [hcoord 0, hcoord 1, mulVecPair_zero, mulVecPair_one,
      Matrix.det_fin_two, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_sub,
      map_mul, map_mul]
    linear_combination
      (algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 0 0) *
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 1 1) -
        algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 0 1) *
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 1 0)) * hweq

omit [IsFractionRing R K] in
/-- A matrix `M ∈ GL₂(R)` maps `interLattice R K ϖ c d` onto `interLattice R K ϖ x y`, where
`(x, y) = M (c, d)ᵀ`. -/
theorem latticeMap_map_interLattice (M : Matrix.GeneralLinearGroup (Fin 2) R)
    (ϖ c d : R) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) =
      interLattice R K ϖ (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
        (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) := by
  refine le_antisymm (latticeMap_map_interLattice_le M ϖ c d) ?_
  have hinv := latticeMap_map_interLattice_le (K := K) M⁻¹ ϖ
    (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
    (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1)
  have hcomp : ∀ i : Fin 2, mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) i = ![c, d] i := by
    intro i
    rw [← mulVecPair_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    change ((1 : Matrix (Fin 2) (Fin 2) R) *ᵥ ![c, d]) i = ![c, d] i
    rw [Matrix.one_mulVec]
  rw [show mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) 0 = c from hcomp 0,
    show mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) 1 = d from hcomp 1] at hinv
  have hmono := latticeMap_mono (R := R)
    (Matrix.GeneralLinearGroup.map (algebraMap R K) M) hinv
  rwa [← latticeMap_mul, ← map_mul, mul_inv_cancel, map_one, latticeMap_one] at hmono

end Engine

section Dichotomy

variable [IsFractionRing R K]

omit [IsFractionRing R K] in
/-- `interLattice R K ϖ c d` depends only on `(c, d)` modulo `ϖ`. -/
theorem interLattice_congr {ϖ c d c' d' : R} (hc : ϖ ∣ c - c') (hd : ϖ ∣ d - d') :
    interLattice R K ϖ c d = interLattice R K ϖ c' d' := by
  have key : ∀ {a b a' b' : R}, ϖ ∣ a - a' → ϖ ∣ b - b' →
      interLattice R K ϖ a b ≤ interLattice R K ϖ a' b' := by
    rintro a b a' b' ⟨x, hx⟩ ⟨y, hy⟩ v ⟨hv, w, hw, hweq⟩
    obtain ⟨r0, hr0⟩ := hv 0
    obtain ⟨r1, hr1⟩ := hv 1
    refine ⟨hv, w - algebraMap R K y * algebraMap R K r0 +
        algebraMap R K x * algebraMap R K r1,
      IsLocalization.isInteger_add
        (IsLocalization.isInteger_sub hw (IsLocalization.isInteger_mul ⟨y, rfl⟩ ⟨r0, rfl⟩))
        (IsLocalization.isInteger_mul ⟨x, rfl⟩ ⟨r1, rfl⟩), ?_⟩
    have ha' : algebraMap R K a' =
        algebraMap R K a - algebraMap R K ϖ * algebraMap R K x := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hx)
    have hb' : algebraMap R K b' =
        algebraMap R K b - algebraMap R K ϖ * algebraMap R K y := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hy)
    rw [ha', hb']
    linear_combination hweq + algebraMap R K ϖ * algebraMap R K y * hr0 -
      algebraMap R K ϖ * algebraMap R K x * hr1
  exact le_antisymm (key hc hd) (key (dvd_sub_comm.mp hc) (dvd_sub_comm.mp hd))

omit [IsFractionRing R K] in
/-- `interLattice R K ϖ c d` does not change when `(c, d)` is multiplied by a unit. -/
theorem interLattice_unit_mul (ϖ : R) (u : Rˣ) (c d : R) :
    interLattice R K ϖ ((u : R) * c) ((u : R) * d) = interLattice R K ϖ c d := by
  have hu : algebraMap R K ((u⁻¹ : Rˣ) : R) * algebraMap R K (u : R) = 1 := by
    rw [← map_mul, ← map_one (algebraMap R K)]
    exact congrArg _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  ext v
  rw [mem_interLattice, mem_interLattice]
  constructor
  · rintro ⟨hv, w, hw, hweq⟩
    refine ⟨hv, algebraMap R K ((u⁻¹ : Rˣ) : R) * w,
      IsLocalization.isInteger_mul ⟨_, rfl⟩ hw, ?_⟩
    rw [map_mul, map_mul] at hweq
    calc algebraMap R K d * v 0 - algebraMap R K c * v 1
        = algebraMap R K ((u⁻¹ : Rˣ) : R) *
            (algebraMap R K (u : R) * algebraMap R K d * v 0 -
              algebraMap R K (u : R) * algebraMap R K c * v 1) := by
          rw [mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, hu, one_mul,
            one_mul]
      _ = algebraMap R K ϖ * (algebraMap R K ((u⁻¹ : Rˣ) : R) * w) := by
          rw [hweq]; ring
  · rintro ⟨hv, w, hw, hweq⟩
    refine ⟨hv, algebraMap R K (u : R) * w, IsLocalization.isInteger_mul ⟨_, rfl⟩ hw, ?_⟩
    rw [map_mul, map_mul]
    calc algebraMap R K (u : R) * algebraMap R K d * v 0 -
          algebraMap R K (u : R) * algebraMap R K c * v 1
        = algebraMap R K (u : R) * (algebraMap R K d * v 0 - algebraMap R K c * v 1) := by
          ring
      _ = algebraMap R K ϖ * (algebraMap R K (u : R) * w) := by rw [hweq]; ring

omit [IsFractionRing R K] in
/-- Let `M ∈ GL₂(R)` and `λ ∈ Rˣ`. If `M (c, d)ᵀ ≡ λ (c, d)` modulo `ϖ`, then `M` maps
`interLattice R K ϖ c d` onto itself. -/
theorem latticeMap_map_interLattice_eq_self (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (lam : Rˣ)
    (h0 : ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 - (lam : R) * c)
    (h1 : ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 - (lam : R) * d) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) =
      interLattice R K ϖ c d := by
  rw [latticeMap_map_interLattice, interLattice_congr h0 h1, interLattice_unit_mul]

theorem dvd_of_latticeMap_map_interLattice_eq_self
    (M : Matrix.GeneralLinearGroup (Fin 2) R) {ϖ c d : R}
    (h : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) = interLattice R K ϖ c d) :
    ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 := by
  rw [latticeMap_map_interLattice] at h
  exact dvd_of_interLattice_eq h

end Dichotomy

section Rigidity

variable [IsFractionRing R K]

omit [Algebra R K] [IsFractionRing R K] in
/-- If `a b = ϖ²` for a prime `ϖ`, then `a` or `b` is a unit, or `a` is associated to `ϖ`. -/
private theorem isUnit_or_isUnit_or_associated_of_mul_eq_sq [IsDomain R] {ϖ a b : R}
    (hϖ : Prime ϖ) (h : a * b = ϖ * ϖ) :
    IsUnit a ∨ IsUnit b ∨ ∃ u : R, IsUnit u ∧ a = ϖ * u := by
  obtain ⟨i, hi, u, hu⟩ := (dvd_prime_pow hϖ 2).mp ⟨b, by rw [sq, h]⟩
  rcases i with _ | _ | _ | i
  · exact Or.inl (IsUnit.of_mul_eq_one (u : R) (hu.trans (pow_zero ϖ)))
  · exact Or.inr (Or.inr ⟨↑u⁻¹, (u⁻¹).isUnit, (Units.eq_mul_inv_iff_mul_eq u).mpr
      (hu.trans (pow_one ϖ))⟩)
  · have ha : a ≠ 0 := fun ha => hϖ.ne_zero (mul_self_eq_zero.mp (by rw [← h, ha, zero_mul]))
    have hub : (u : R) = b := mul_left_cancel₀ ha (hu.trans ((sq ϖ).trans h.symm))
    exact Or.inr (Or.inl (hub ▸ u.isUnit))
  · omega

omit [IsFractionRing R K] in
theorem latticeMap_scalarGL_eq_self_of_isUnit {e : Kˣ} {u : R} (hu : IsUnit u)
    (heu : (e : K) = algebraMap R K u) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL e) L = L := by
  obtain ⟨v, rfl⟩ := hu
  ext x
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [heu, algebraMap_smul]
    exact L.smul_mem _ hw
  · intro hx
    refine ⟨((v⁻¹ : Rˣ) : R) • x, L.smul_mem _ hx, ?_⟩
    rw [heu, algebraMap_smul, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul]

theorem isInteger_mul_algebraMap_of_latticeMap_le {e : Kˣ} {ϖ : R} (hϖ : ϖ ≠ 0)
    {N : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ N)
    (hup : latticeMap (scalarGL e) N ≤ stdLattice R K) :
    IsLocalization.IsInteger R ((e : K) * algebraMap R K ϖ) := by
  have h1 : (algebraMap R K ϖ) • (Pi.single 0 1 : Fin 2 → K) ∈
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
    rw [mem_latticeMap_scalarGL]
    exact ⟨Pi.single 0 1, single_one_mem_stdLattice R K 0, by rw [unitOfNeZero_coe]⟩
  have h2 : (e : K) • ((algebraMap R K ϖ) • (Pi.single 0 1 : Fin 2 → K)) ∈
      latticeMap (scalarGL e) N := by
    rw [mem_latticeMap_scalarGL]
    exact ⟨_, hlow h1, rfl⟩
  have h3 := hup h2 0
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
  exact h3

theorem latticeMap_scalarGL_inv_le_of_mul_eq_unit {e : Kˣ} {ϖ : R} (hϖ : ϖ ≠ 0) {u : R}
    (hu : IsUnit u) (heu : (e : K) * algebraMap R K ϖ = algebraMap R K u)
    {N : Submodule R (Fin 2 → K)} (hN : N ≤ stdLattice R K) :
    latticeMap (scalarGL e⁻¹) N ≤
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
  obtain ⟨v, rfl⟩ := hu
  have hprod : (e : K) *
      (algebraMap R K ϖ * algebraMap R K ((v⁻¹ : Rˣ) : R)) = 1 := by
    rw [← mul_assoc, heu, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      map_one]
  have hinv : ((e⁻¹ : Kˣ) : K) =
      algebraMap R K ϖ * algebraMap R K ((v⁻¹ : Rˣ) : R) := by
    have h1 := congrArg (fun z => ((e⁻¹ : Kˣ) : K) * z) hprod
    simp only [mul_one] at h1
    rw [← mul_assoc, Units.inv_mul, one_mul] at h1
    exact h1.symm
  intro x hx
  rw [mem_latticeMap_scalarGL] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  rw [mem_latticeMap_scalarGL_stdLattice hϖ]
  intro i
  obtain ⟨wi, hwi⟩ := hN hw i
  refine ⟨algebraMap R K ((v⁻¹ : Rˣ) : R) * algebraMap R K wi,
    IsLocalization.isInteger_mul ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hinv, ← hwi]
  ring

/-- For a prime `ϖ` of a domain `R` with fraction field `K`, two homothetic `R`-submodules `N` and
`N'` of `K²` with `ϖ R² < N ≤ R²` and `ϖ R² < N' ≤ R²` are equal. -/
theorem eq_of_homothetic_of_mem_interval [IsDomain R] {ϖ : R} (hϖ : Prime ϖ)
    {N N' : Submodule R (Fin 2 → K)}
    (hNlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < N)
    (hNup : N ≤ stdLattice R K)
    (hN'low : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < N')
    (hN'up : N' ≤ stdLattice R K)
    (h : Homothetic N N') : N = N' := by
  obtain ⟨e, he⟩ := h
  have hNinv : latticeMap (scalarGL e⁻¹) N' = N := by
    rw [← he, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one,
      latticeMap_one]
  obtain ⟨a, ha⟩ := isInteger_mul_algebraMap_of_latticeMap_le hϖ.ne_zero hNlow.le
    (he ▸ hN'up)
  obtain ⟨b, hb⟩ := isInteger_mul_algebraMap_of_latticeMap_le hϖ.ne_zero hN'low.le
    (hNinv ▸ hNup)
  have hϖK : algebraMap R K ϖ ≠ 0 := fun h0 =>
    hϖ.ne_zero (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
  have hab : a * b = ϖ * ϖ := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ha, hb]
    calc (e : K) * algebraMap R K ϖ * (((e⁻¹ : Kˣ) : K) * algebraMap R K ϖ)
        = ((e : K) * ((e⁻¹ : Kˣ) : K)) * (algebraMap R K ϖ * algebraMap R K ϖ) := by
          ring
      _ = algebraMap R K ϖ * algebraMap R K ϖ := by rw [Units.mul_inv, one_mul]
  rcases isUnit_or_isUnit_or_associated_of_mul_eq_sq hϖ hab with hua | hub | ⟨u, hu, hau⟩
  · exfalso
    have hkey := latticeMap_scalarGL_inv_le_of_mul_eq_unit (e := e) hϖ.ne_zero hua
      ha.symm hN'up
    rw [hNinv] at hkey
    exact absurd (le_antisymm hkey hNlow.le) hNlow.ne'
  · exfalso
    have hkey := latticeMap_scalarGL_inv_le_of_mul_eq_unit (e := e⁻¹) hϖ.ne_zero hub
      hb.symm hNup
    rw [inv_inv, he] at hkey
    exact absurd (le_antisymm hkey hN'low.le) hN'low.ne'
  · have heu : (e : K) = algebraMap R K u := by
      have h2 : (e : K) * algebraMap R K ϖ = algebraMap R K u * algebraMap R K ϖ := by
        rw [← ha, hau, map_mul]; ring
      exact mul_right_cancel₀ hϖK h2
    rw [← he, latticeMap_scalarGL_eq_self_of_isUnit hu heu]

omit [Algebra R K] [IsFractionRing R K] in
/-- If `ϖ` divides both coordinates of `M (c, d)ᵀ` for `M ∈ GL₂(R)`, it divides `c` and `d`. -/
private theorem dvd_and_dvd_of_dvd_mulVecPair (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (h : ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 ∧
      ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) :
    ϖ ∣ c ∧ ϖ ∣ d := by
  have hcomp : ∀ i : Fin 2, mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) i = ![c, d] i := by
    intro i
    rw [← mulVecPair_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    change ((1 : Matrix (Fin 2) (Fin 2) R) *ᵥ ![c, d]) i = ![c, d] i
    rw [Matrix.one_mulVec]
  have h0 := hcomp 0
  have h1 := hcomp 1
  rw [mulVecPair_zero, Matrix.cons_val_zero] at h0
  rw [mulVecPair_one, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  exact ⟨h0 ▸ dvd_add (dvd_mul_of_dvd_right h.1 _) (dvd_mul_of_dvd_right h.2 _),
    h1 ▸ dvd_add (dvd_mul_of_dvd_right h.1 _) (dvd_mul_of_dvd_right h.2 _)⟩

/-- Let `R` be a domain with fraction field `K`, let `M ∈ GL₂(R)`, let `ϖ` be prime and let `ϖ` not
divide both `c` and `d`. If `interLattice R K ϖ c d` is a full lattice and `M` fixes its vertex,
then `ϖ ∣ d x - c y` for `(x, y) = M (c, d)ᵀ`: the pairs `(c, d)` and `M (c, d)ᵀ` are linearly
dependent modulo `ϖ`. -/
theorem dvd_of_isFixedVertex_interLattice [IsDomain R]
    (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (hϖ : Prime ϖ) (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d))
    {hL : Submodule.IsFullLattice K (interLattice R K ϖ c d)}
    (h : IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
      (Vertex.mk R K (interLattice R K ϖ c d) hL)) :
    ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 := by
  have hcd' : ¬(ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 ∧
      ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) :=
    fun h' => hcd (dvd_and_dvd_of_dvd_mulVecPair M h')
  rw [isFixedVertex_mk_iff, latticeMap_map_interLattice] at h
  have heq := eq_of_homothetic_of_mem_interval hϖ
    (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd')
    (interLattice_le_stdLattice _ _ _)
    (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd)
    (interLattice_le_stdLattice _ _ _) h
  exact dvd_of_interLattice_eq heq

theorem not_isFixedVertex_interLattice_of_not_dvd [IsDomain R]
    (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (hϖ : Prime ϖ) (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d))
    (hnofix : ¬ ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1)
    {hL : Submodule.IsFullLattice K (interLattice R K ϖ c d)} :
    ¬ IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
      (Vertex.mk R K (interLattice R K ϖ c d) hL) :=
  fun h => hnofix (dvd_of_isFixedVertex_interLattice M hϖ hcd h)

end Rigidity

section FullLattice

variable [IsFractionRing R K]

/-- Over a Noetherian ring `R` with fraction field `K`, for `ϖ ≠ 0` every `R`-submodule between
`ϖ R²` and `R²` is a full lattice. -/
theorem isFullLattice_of_le_of_le [IsNoetherianRing R] {ϖ : R} (hϖ : ϖ ≠ 0)
    {N : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ N)
    (hup : N ≤ stdLattice R K) : Submodule.IsFullLattice K N :=
  haveI := IsFullLattice.map (isFullLattice_stdLattice (R := R) (K := K))
    (scalarGL (unitOfNeZero (K := K) hϖ))
  Submodule.IsFullLattice.of_le_of_fg K hlow ((stdLattice_fg R K).of_le hup)

/-- Over a Noetherian ring `R` with fraction field `K`, for an irreducible `ϖ` every
`interLattice R K ϖ c d` is a full lattice. -/
theorem isFullLattice_interLattice [IsNoetherianRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    (c d : R) : Submodule.IsFullLattice K (interLattice R K ϖ c d) :=
  isFullLattice_of_le_of_le hϖ.ne_zero
    (latticeMap_scalarGL_le_interLattice hϖ.ne_zero c d)
    (interLattice_le_stdLattice ϖ c d)

end FullLattice

/-- The twisted action `v ↦ δ σ(v)` on vertices. -/
def Vertex.twistedAct (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (v : Vertex R K) : Vertex R K :=
  Vertex.act δ (Vertex.galAct σ v)

theorem Vertex.twistedAct_mk (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) (hL : Submodule.IsFullLattice K L) :
    Vertex.twistedAct δ σ (Vertex.mk R K L hL) =
      Vertex.mk R K (twistedLatticeMap δ σ L) (IsFullLattice.twisted hL δ σ) :=
  rfl

theorem Vertex.galAct_refl (v : Vertex R K) :
    Vertex.galAct (IntegralAut.refl R K) v = v := by
  induction v using Quotient.inductionOn with
  | h L =>
    obtain ⟨L, hL⟩ := L
    change Vertex.galAct (IntegralAut.refl R K) (Vertex.mk R K L hL) =
      Vertex.mk R K L hL
    rw [Vertex.galAct_mk, Vertex.mk_eq_mk_iff, latticeGal_refl]
    exact Homothetic.refl _

theorem Vertex.twistedAct_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (v : Vertex R K) :
    Vertex.twistedAct δ (IntegralAut.refl R K) v = Vertex.act δ v := by
  rw [Vertex.twistedAct, Vertex.galAct_refl]

/-- `v` is fixed by the twisted action of `(δ, σ)`. -/
def IsTwistedFixedVertex (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (v : Vertex R K) : Prop :=
  Vertex.twistedAct δ σ v = v

/-- The set of vertices fixed by the twisted action of `(δ, σ)`. -/
def twistedFixedVertexSet (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : Set (Vertex R K) :=
  {v | IsTwistedFixedVertex δ σ v}

theorem mem_twistedFixedVertexSet {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    {σ : IntegralAut R K} {v : Vertex R K} :
    v ∈ twistedFixedVertexSet δ σ ↔ Vertex.twistedAct δ σ v = v :=
  Iff.rfl

attribute [local simp] mem_twistedFixedVertexSet
/-- The number of vertices fixed by the twisted action of `(δ, σ)` (`0` if infinite). -/
noncomputable def twistedUnitOrbitalCount (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : ℕ :=
  Nat.card (twistedFixedVertexSet δ σ)

theorem twistedFixedVertexSet_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedFixedVertexSet δ (IntegralAut.refl R K) = fixedVertexSet (R := R) δ := by
  ext v
  rw [mem_twistedFixedVertexSet, mem_fixedVertexSet, Vertex.twistedAct_refl]

theorem twistedUnitOrbitalCount_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedUnitOrbitalCount δ (IntegralAut.refl R K) = unitOrbitalCount R δ := by
  rw [twistedUnitOrbitalCount, unitOrbitalCount, twistedFixedVertexSet_refl]

theorem Vertex.twistedAct_three_of_orderThree (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (v : Vertex R K) :
    Vertex.twistedAct δ σ (Vertex.twistedAct δ σ (Vertex.twistedAct δ σ v)) =
      Vertex.act (normThree δ σ) v := by
  induction v using Quotient.inductionOn with
  | h L =>
    obtain ⟨L, hL⟩ := L
    change Vertex.twistedAct δ σ (Vertex.twistedAct δ σ (Vertex.twistedAct δ σ
      (Vertex.mk R K L hL))) = Vertex.act (normThree δ σ) (Vertex.mk R K L hL)
    rw [Vertex.twistedAct_mk, Vertex.twistedAct_mk, Vertex.twistedAct_mk, Vertex.act_mk,
      Vertex.mk_eq_mk_iff, twistedLatticeMap_three_of_orderThree δ hσ]
    exact Homothetic.refl _

theorem Vertex.twistedAct_two_of_orderTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : σ.comp σ = IntegralAut.refl R K) (v : Vertex R K) :
    Vertex.twistedAct δ σ (Vertex.twistedAct δ σ v) = Vertex.act (normTwo δ σ) v := by
  induction v using Quotient.inductionOn with
  | h L =>
    obtain ⟨L, hL⟩ := L
    change Vertex.twistedAct δ σ (Vertex.twistedAct δ σ (Vertex.mk R K L hL)) =
      Vertex.act (normTwo δ σ) (Vertex.mk R K L hL)
    rw [Vertex.twistedAct_mk, Vertex.twistedAct_mk, Vertex.act_mk, Vertex.mk_eq_mk_iff,
      twistedLatticeMap_two_of_orderTwo δ hσ]
    exact Homothetic.refl _

theorem isFixedVertex_normThree_of_isTwistedFixedVertex
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K) {v : Vertex R K}
    (hv : IsTwistedFixedVertex δ σ v) : IsFixedVertex (normThree δ σ) v := by
  have hv' : Vertex.twistedAct δ σ v = v := hv
  change Vertex.act (normThree δ σ) v = v
  rw [← Vertex.twistedAct_three_of_orderThree δ hσ, hv', hv', hv']

theorem isFixedVertex_normTwo_of_isTwistedFixedVertex
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K) {v : Vertex R K}
    (hv : IsTwistedFixedVertex δ σ v) : IsFixedVertex (normTwo δ σ) v := by
  have hv' : Vertex.twistedAct δ σ v = v := hv
  change Vertex.act (normTwo δ σ) v = v
  rw [← Vertex.twistedAct_two_of_orderTwo δ hσ, hv', hv']

/-- If `σ³ = id`, twisted fixed vertices are fixed by `normThree δ σ`. -/
theorem twistedFixedVertexSet_subset_fixedVertexSet_normThree
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K) :
    twistedFixedVertexSet δ σ ⊆ fixedVertexSet (R := R) (normThree δ σ) :=
  fun _ hv => isFixedVertex_normThree_of_isTwistedFixedVertex δ hσ hv

/-- If `σ² = id`, twisted fixed vertices are fixed by `normTwo δ σ`. -/
theorem twistedFixedVertexSet_subset_fixedVertexSet_normTwo
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K) :
    twistedFixedVertexSet δ σ ⊆ fixedVertexSet (R := R) (normTwo δ σ) :=
  fun _ hv => isFixedVertex_normTwo_of_isTwistedFixedVertex δ hσ hv

theorem isTwistedFixedVertex_stdVertex_of_mem_range [IsFractionRing R K]
    {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hδ : δ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (σ : IntegralAut R K) :
    IsTwistedFixedVertex δ σ (stdVertex R K) := by
  change Vertex.twistedAct δ σ (stdVertex R K) = stdVertex R K
  rw [Vertex.twistedAct, Vertex.galAct_stdVertex]
  exact isFixedVertex_stdVertex_of_mem_range hδ

theorem nonempty_twistedFixedVertexSet_of_mem_range [IsFractionRing R K]
    {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hδ : δ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (σ : IntegralAut R K) :
    (twistedFixedVertexSet δ σ).Nonempty :=
  ⟨stdVertex R K, isTwistedFixedVertex_stdVertex_of_mem_range hδ σ⟩

theorem twistedFixedVertexSet_eq_singleton_of_subset_subsingleton
    {δ : Matrix.GeneralLinearGroup (Fin 2) K} {σ : IntegralAut R K}
    {s : Set (Vertex R K)} (hincl : twistedFixedVertexSet δ σ ⊆ s)
    (hsub : s.Subsingleton) {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedFixedVertexSet δ σ = {v₀} :=
  Set.eq_singleton_iff_unique_mem.mpr
    ⟨hv₀, fun _ hw => hsub (hincl hw) (hincl hv₀)⟩

theorem twistedUnitOrbitalCount_eq_one_of_subset_subsingleton
    {δ : Matrix.GeneralLinearGroup (Fin 2) K} {σ : IntegralAut R K}
    {s : Set (Vertex R K)} (hincl : twistedFixedVertexSet δ σ ⊆ s)
    (hsub : s.Subsingleton) {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedUnitOrbitalCount δ σ = 1 := by
  rw [twistedUnitOrbitalCount,
    twistedFixedVertexSet_eq_singleton_of_subset_subsingleton hincl hsub hv₀,
    Nat.card_coe_set_eq, Set.ncard_singleton]

theorem unitOrbitalCount_eq_one_of_subsingleton
    {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hsub : (fixedVertexSet (R := R) γ).Subsingleton) {w₀ : Vertex R K}
    (hw₀ : IsFixedVertex γ w₀) : unitOrbitalCount R γ = 1 := by
  have heq : fixedVertexSet (R := R) γ = {w₀} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hw₀, fun _ hx => hsub hx hw₀⟩
  rw [unitOrbitalCount, heq, Nat.card_coe_set_eq, Set.ncard_singleton]

theorem twistedUnitOrbitalCount_eq_one_of_subsingleton_normThree
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (hsub : (fixedVertexSet (R := R) (normThree δ σ)).Subsingleton)
    {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedUnitOrbitalCount δ σ = 1 :=
  twistedUnitOrbitalCount_eq_one_of_subset_subsingleton
    (twistedFixedVertexSet_subset_fixedVertexSet_normThree δ hσ) hsub hv₀

theorem twistedUnitOrbitalCount_eq_one_of_subsingleton_normTwo
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K)
    (hsub : (fixedVertexSet (R := R) (normTwo δ σ)).Subsingleton)
    {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedUnitOrbitalCount δ σ = 1 :=
  twistedUnitOrbitalCount_eq_one_of_subset_subsingleton
    (twistedFixedVertexSet_subset_fixedVertexSet_normTwo δ hσ) hsub hv₀

section SingletonCounts

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']

/-- If `σ³ = id`, `normThree δ σ` has at most one fixed vertex, `δ` has a twisted fixed vertex, and
`γ` has exactly one fixed vertex, then the twisted fixed-vertex count of `(δ, σ)` equals the
fixed-vertex count of `γ`: both are `1`. -/
theorem twistedUnitOrbitalCount_eq_unitOrbitalCount_of_subsingleton
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (hsub_up : (fixedVertexSet (R := R) (normThree δ σ)).Subsingleton)
    {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀)
    (γ : Matrix.GeneralLinearGroup (Fin 2) K')
    (hsub_down : (fixedVertexSet (R := R') γ).Subsingleton)
    {w₀ : Vertex R' K'} (hw₀ : IsFixedVertex γ w₀) :
    twistedUnitOrbitalCount δ σ = unitOrbitalCount R' γ := by
  rw [twistedUnitOrbitalCount_eq_one_of_subsingleton_normThree δ hσ hsub_up hv₀,
    unitOrbitalCount_eq_one_of_subsingleton hsub_down hw₀]

/-- The analogue of `twistedUnitOrbitalCount_eq_unitOrbitalCount_of_subsingleton` for `σ² = id`,
with `normTwo δ σ`. -/
theorem twistedUnitOrbitalCount_eq_unitOrbitalCount_of_subsingleton_two
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K)
    (hsub_up : (fixedVertexSet (R := R) (normTwo δ σ)).Subsingleton)
    {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀)
    (γ : Matrix.GeneralLinearGroup (Fin 2) K')
    (hsub_down : (fixedVertexSet (R := R') γ).Subsingleton)
    {w₀ : Vertex R' K'} (hw₀ : IsFixedVertex γ w₀) :
    twistedUnitOrbitalCount δ σ = unitOrbitalCount R' γ := by
  rw [twistedUnitOrbitalCount_eq_one_of_subsingleton_normTwo δ hσ hsub_up hv₀,
    unitOrbitalCount_eq_one_of_subsingleton hsub_down hw₀]

end SingletonCounts

theorem latticeGal_interLattice_le (σ : IntegralAut R K) (ϖ c d : R) :
    latticeGal σ (interLattice R K ϖ c d) ≤
      interLattice R K (σ.toBase ϖ) (σ.toBase c) (σ.toBase d) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwint, t, ht, hweq⟩ := hw
  refine ⟨fun i => σ.isInteger_map (hwint i), σ.toField t, σ.isInteger_map ht, ?_⟩
  have key : algebraMap R K (σ.toBase d) * σ.toField (w 0) -
      algebraMap R K (σ.toBase c) * σ.toField (w 1) =
        algebraMap R K (σ.toBase ϖ) * σ.toField t := by
    rw [← σ.commutes d, ← σ.commutes c, ← σ.commutes ϖ]
    calc σ.toField (algebraMap R K d) * σ.toField (w 0) -
          σ.toField (algebraMap R K c) * σ.toField (w 1)
        = σ.toField (algebraMap R K d * w 0 - algebraMap R K c * w 1) := by
          rw [map_sub, map_mul, map_mul]
      _ = σ.toField (algebraMap R K ϖ * t) := by rw [hweq]
      _ = σ.toField (algebraMap R K ϖ) * σ.toField t := by rw [map_mul]
  rw [galVec_apply, galVec_apply]
  exact key

/-- An integral automorphism `σ` maps `interLattice R K ϖ c d` onto
`interLattice R K (σ ϖ) (σ c) (σ d)`. -/
theorem latticeGal_interLattice (σ : IntegralAut R K) (ϖ c d : R) :
    latticeGal σ (interLattice R K ϖ c d) =
      interLattice R K (σ.toBase ϖ) (σ.toBase c) (σ.toBase d) := by
  refine le_antisymm (latticeGal_interLattice_le σ ϖ c d) ?_
  have h := latticeGal_interLattice_le σ.symm (σ.toBase ϖ) (σ.toBase c) (σ.toBase d)
  rw [IntegralAut.symm_toBase, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply] at h
  intro v hv
  exact ⟨galVec σ.symm v, h (galVec_mem_latticeGal hv), galVec_galVec_symm σ v⟩

theorem twistedLatticeMap_map_interLattice (δ : Matrix.GeneralLinearGroup (Fin 2) R)
    (σ : IntegralAut R K) {ϖ : R} (hϖ : σ.toBase ϖ = ϖ) (c d : R) :
    twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ
        (interLattice R K ϖ c d) =
      interLattice R K ϖ
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 0)
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 1) := by
  rw [twistedLatticeMap, latticeGal_interLattice, hϖ, latticeMap_map_interLattice]

theorem dvd_of_twistedLatticeMap_map_interLattice_eq_self [IsFractionRing R K]
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (σ : IntegralAut R K) {ϖ : R}
    (hϖ : σ.toBase ϖ = ϖ) {c d : R}
    (h : twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ
        (interLattice R K ϖ c d) = interLattice R K ϖ c d) :
    ϖ ∣ d * mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 0 -
        c * mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 1 := by
  rw [twistedLatticeMap_map_interLattice δ σ hϖ c d] at h
  exact dvd_of_interLattice_eq h

end LT.LatticeTree

end
