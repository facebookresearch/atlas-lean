/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryActiveGlobalSplit
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryResidualReduction

/-!
# Global reindexing of active Shih boundary faces
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

/-- The exceptional zero-left-degree active family. -/
abbrev ShihLeftEdgeData (n : ℕ) := Fin (n + 1) × Fin 2

/-- All inserted-left active upper coordinates based at degree `n`. -/
abbrev ShihLeftInsertionData (n : ℕ) :=
  Σ i : ShihIndex n, Fin (i.p + 3)

/-- All inserted-right active upper coordinates based at degree `n`. -/
abbrev ShihRightInsertionData (n : ℕ) :=
  Σ i : ShihIndex n, Fin (i.q + 2)

def ShihIndex.leftUpperLocalFaceOf {n : ℕ} (i : ShihIndex n)
    (a : Fin (i.p + 3)) :
    Fin ((i.leftUpperOf a).p + 1 + (i.leftUpperOf a).q + 1) :=
  Fin.cast (by simp [ShihIndex.leftUpperOf])
    (Shuffle.leftBoundaryIndex i.shuffle a)

@[simp]
theorem ShihIndex.leftUpperOf_gap {n : ℕ} (i : ShihIndex n)
    (a : Fin (i.p + 3)) : (i.leftUpperOf a).gap = i.gap := by
  simp [ShihIndex.leftUpperOf, ShihIndex.gap]

def ShihIndex.rightUpperLocalFaceOf {n : ℕ} (i : ShihIndex n)
    (b : Fin (i.q + 2)) :
    Fin ((i.rightUpperOf b).p + 1 + (i.rightUpperOf b).q + 1) :=
  Fin.cast (by simp [ShihIndex.rightUpperOf])
    (Shuffle.rightBoundaryIndex i.shuffle b)

@[simp]
theorem ShihIndex.rightUpperOf_gap {n : ℕ} (i : ShihIndex n)
    (b : Fin (i.q + 2)) : (i.rightUpperOf b).gap = i.gap := by
  simp [ShihIndex.rightUpperOf, ShihIndex.gap]
  omega

def ShihIndex.leftEdgeLocalFace (N : ℕ) (q : Fin N) (a : Fin 2) :
    Fin ((leftEdgeIndex N q a).p + 1 + (leftEdgeIndex N q a).q + 1) :=
  Fin.cast (by simp [leftEdgeIndex])
    (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle q) a)

def leftEdgeToActive {n : ℕ} (z : ShihLeftEdgeData n) :
    ShihUpperNonmixedData n := by
  let w : ShihUpperActiveData n :=
    ⟨ShihIndex.leftEdgeIndex (n + 1) z.1 z.2,
      ShihIndex.leftEdgeLocalFace (n + 1) z.1 z.2⟩
  refine ⟨w, ?_⟩
  apply Shuffle.isLeftBoundary_not_isMixedBoundary
  simpa only [w, ShihUpperActiveData.IsMixed,
    ShihIndex.leftEdgeIndex, ShihIndex.leftEdgeLocalFace,
    Shuffle.leftBoundaryPair, Fin.cast_eq_self] using
      Shuffle.leftBoundaryPair_isLeftBoundary
        (z.2, Shuffle.leftUnitShuffle z.1.val)

def leftInsertionToActive {n : ℕ} (z : ShihLeftInsertionData n) :
    ShihUpperNonmixedData n := by
  let w : ShihUpperActiveData n :=
    ⟨z.1.leftUpperOf z.2, z.1.leftUpperLocalFaceOf z.2⟩
  refine ⟨w, ?_⟩
  apply Shuffle.isLeftBoundary_not_isMixedBoundary
  simpa only [w, ShihUpperActiveData.IsMixed,
    ShihIndex.leftUpperOf, ShihIndex.leftUpperLocalFaceOf,
    Shuffle.leftBoundaryPair, Fin.cast_eq_self] using
      Shuffle.leftBoundaryPair_isLeftBoundary (z.2, z.1.shuffle)

def rightInsertionToActive {n : ℕ} (z : ShihRightInsertionData n) :
    ShihUpperNonmixedData n := by
  let w : ShihUpperActiveData n :=
    ⟨z.1.rightUpperOf z.2, z.1.rightUpperLocalFaceOf z.2⟩
  refine ⟨w, ?_⟩
  apply Shuffle.isRightBoundary_not_isMixedBoundary
  simpa only [w, ShihUpperActiveData.IsMixed,
    ShihIndex.rightUpperOf, ShihIndex.rightUpperLocalFaceOf,
    Shuffle.rightBoundaryPair, Fin.cast_eq_self] using
      Shuffle.rightBoundaryPair_isRightBoundary (z.2, z.1.shuffle)

/-- The three canonical families of nonmixed active upper faces. -/
abbrev ShihActiveBoundaryData (n : ℕ) :=
  ShihLeftEdgeData n ⊕
    (ShihLeftInsertionData n ⊕ ShihRightInsertionData n)

/-- Assemble an exceptional edge or ordinary insertion coordinate into the
canonical nonmixed active data. -/
def activeBoundaryDataToNonmixed {n : ℕ} :
    ShihActiveBoundaryData n → ShihUpperNonmixedData n
  | Sum.inl z => leftEdgeToActive z
  | Sum.inr (Sum.inl z) => leftInsertionToActive z
  | Sum.inr (Sum.inr z) => rightInsertionToActive z

theorem activeBoundaryDataToNonmixed_surjective {n : ℕ} :
    Function.Surjective (@activeBoundaryDataToNonmixed n) := by
  rintro ⟨⟨⟨p, q, s⟩, r⟩, hnm⟩
  by_cases hp : p = 0
  · subst p
    change Fin (n + 1) at q
    change Shuffle 1 q at s
    change Fin (1 + q + 1) at r
    by_cases hq : q = 0
    · subst q
      let w : Shuffle.NonmixedBoundaryFace 1 0 := ⟨(s, r), hnm⟩
      let y := (Shuffle.leftBoundaryEquivNonmixedRightZero (p := 0)).symm w
      let x := (Shuffle.leftBoundaryEquiv (p := 0) (q := 0)).symm y
      have hy : y.val = w.val := congrArg Subtype.val
        ((Shuffle.leftBoundaryEquivNonmixedRightZero (p := 0)).apply_symm_apply w)
      have hx : Shuffle.leftBoundaryPair x = y.val := congrArg Subtype.val
        ((Shuffle.leftBoundaryEquiv (p := 0) (q := 0)).apply_symm_apply y)
      rcases x with ⟨a, t⟩
      rw [Shuffle.eq_leftUnitShuffle t] at hx
      refine ⟨Sum.inl (⟨0, a⟩), ?_⟩
      apply Subtype.ext
      dsimp only [activeBoundaryDataToNonmixed, leftEdgeToActive]
      have hpair := hx.trans hy
      cases hpair
      rfl
    · obtain ⟨q₀, hq₀⟩ := Fin.eq_succ_of_ne_zero hq
      subst q
      let w : Shuffle.NonmixedBoundaryFace 1 (q₀ + 1) := ⟨(s, r), hnm⟩
      generalize he :
          (Shuffle.nonmixedBoundaryEquiv (p := 0) (q := q₀)).symm w = e
      have heq := (Shuffle.nonmixedBoundaryEquiv
        (p := 0) (q := q₀)).apply_symm_apply w
      rw [he] at heq
      rcases e with y | y
      · let x := (Shuffle.leftBoundaryEquiv (p := 0) (q := q₀ + 1)).symm y
        have hy : (Shuffle.nonmixedBoundaryEquiv (p := 0) (q := q₀)
            (Sum.inl y)).val = w.val := congrArg Subtype.val heq
        have hx : Shuffle.leftBoundaryPair x = y.val := congrArg Subtype.val
          ((Shuffle.leftBoundaryEquiv (p := 0) (q := q₀ + 1)).apply_symm_apply y)
        rcases x with ⟨a, t⟩
        rw [Shuffle.eq_leftUnitShuffle t] at hx
        refine ⟨Sum.inl (q₀.succ, a), ?_⟩
        apply Subtype.ext
        dsimp only [activeBoundaryDataToNonmixed, leftEdgeToActive]
        have hpair := hx.trans hy
        cases hpair
        rfl
      · let x := (Shuffle.rightBoundaryEquiv (p := 1) (q := q₀)).symm y
        have hy : (Shuffle.nonmixedBoundaryEquiv (p := 0) (q := q₀)
            (Sum.inr y)).val = w.val := congrArg Subtype.val heq
        have hx : Shuffle.rightBoundaryPair x = y.val := congrArg Subtype.val
          ((Shuffle.rightBoundaryEquiv (p := 1) (q := q₀)).apply_symm_apply y)
        rcases x with ⟨b, t⟩
        let i : ShihIndex n :=
          { p := ⟨0, Nat.zero_lt_of_lt q₀.isLt⟩
            q := q₀
            shuffle := t }
        refine ⟨Sum.inr (Sum.inr ⟨i, b⟩), ?_⟩
        apply Subtype.ext
        dsimp only [activeBoundaryDataToNonmixed, rightInsertionToActive]
        have hpair := hx.trans hy
        cases hpair
        rfl
  · obtain ⟨p₀, hp₀⟩ := Fin.eq_succ_of_ne_zero hp
    subst p
    rcases q with ⟨q₀, hq₀⟩
    simp only [Fin.val_succ] at hq₀ s r hnm
    have hcard : n + 1 - (p₀.val + 1) = n - p₀.val := by omega
    rw [hcard] at hq₀
    cases q₀ with
    | zero =>
      let w : Shuffle.NonmixedBoundaryFace (p₀ + 2) 0 := ⟨(s, r), hnm⟩
      let y :=
        (Shuffle.leftBoundaryEquivNonmixedRightZero (p := p₀ + 1)).symm w
      let x :=
        (Shuffle.leftBoundaryEquiv (p := p₀ + 1) (q := 0)).symm y
      have hy : y.val = w.val := congrArg Subtype.val
        ((Shuffle.leftBoundaryEquivNonmixedRightZero
          (p := p₀ + 1)).apply_symm_apply w)
      have hx : Shuffle.leftBoundaryPair x = y.val := congrArg Subtype.val
        ((Shuffle.leftBoundaryEquiv (p := p₀ + 1) (q := 0)).apply_symm_apply y)
      rcases x with ⟨a, t⟩
      let i : ShihIndex n :=
        { p := p₀
          q := ⟨0, by omega⟩
          shuffle := t }
      refine ⟨Sum.inr (Sum.inl ⟨i, a⟩), ?_⟩
      apply Subtype.ext
      dsimp only [activeBoundaryDataToNonmixed, leftInsertionToActive]
      have hpair := hx.trans hy
      cases hpair
      rfl
    | succ q₀ =>
      let w : Shuffle.NonmixedBoundaryFace (p₀ + 2) (q₀ + 1) :=
        ⟨(s, r), hnm⟩
      generalize he :
          (Shuffle.nonmixedBoundaryEquiv
            (p := p₀ + 1) (q := q₀)).symm w = e
      have heq := (Shuffle.nonmixedBoundaryEquiv
        (p := p₀ + 1) (q := q₀)).apply_symm_apply w
      rw [he] at heq
      rcases e with y | y
      · let x :=
          (Shuffle.leftBoundaryEquiv (p := p₀ + 1) (q := q₀ + 1)).symm y
        have hy : (Shuffle.nonmixedBoundaryEquiv (p := p₀ + 1) (q := q₀)
            (Sum.inl y)).val = w.val := congrArg Subtype.val heq
        have hx : Shuffle.leftBoundaryPair x = y.val := congrArg Subtype.val
          ((Shuffle.leftBoundaryEquiv
            (p := p₀ + 1) (q := q₀ + 1)).apply_symm_apply y)
        rcases x with ⟨a, t⟩
        let i : ShihIndex n :=
          { p := p₀
            q := ⟨q₀ + 1, hq₀⟩
            shuffle := t }
        refine ⟨Sum.inr (Sum.inl ⟨i, a⟩), ?_⟩
        apply Subtype.ext
        dsimp only [activeBoundaryDataToNonmixed, leftInsertionToActive]
        have hpair := hx.trans hy
        cases hpair
        rfl
      · let x :=
          (Shuffle.rightBoundaryEquiv (p := p₀ + 2) (q := q₀)).symm y
        have hy : (Shuffle.nonmixedBoundaryEquiv (p := p₀ + 1) (q := q₀)
            (Sum.inr y)).val = w.val := congrArg Subtype.val heq
        have hx : Shuffle.rightBoundaryPair x = y.val := congrArg Subtype.val
          ((Shuffle.rightBoundaryEquiv
            (p := p₀ + 2) (q := q₀)).apply_symm_apply y)
        rcases x with ⟨b, t⟩
        let i : ShihIndex n :=
          { p := ⟨p₀ + 1, by omega⟩
            q := ⟨q₀, by
              change q₀ < n - (p₀.val + 1)
              omega⟩
            shuffle := t }
        refine ⟨Sum.inr (Sum.inr ⟨i, b⟩), ?_⟩
        apply Subtype.ext
        dsimp only [activeBoundaryDataToNonmixed, rightInsertionToActive]
        have hpair := hx.trans hy
        cases hpair
        rfl

theorem leftEdgeToActive_injective {n : ℕ} :
    Function.Injective (@leftEdgeToActive n) := by
  rintro ⟨q, a⟩ ⟨q', a'⟩ h
  have hval := congrArg Subtype.val h
  have hindex := congrArg Sigma.fst hval
  have hqHEq := (ShihIndex.mk.inj hindex).2.1
  have hq : q = q' := eq_of_heq hqHEq
  subst q'
  have hshuffleHEq := (ShihIndex.mk.inj hindex).2.2
  have hshuffle :
      Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q) a =
        Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q) a' :=
    eq_of_heq hshuffleHEq
  have hfaceHEq := (Sigma.mk.inj hval).2
  have hface :
      Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle q) a =
        Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle q) a' := by
    apply Fin.ext
    exact congrArg Fin.val (eq_of_heq hfaceHEq)
  have hpair :
      Shuffle.leftBoundaryPair (a, Shuffle.leftUnitShuffle q) =
        Shuffle.leftBoundaryPair (a', Shuffle.leftUnitShuffle q) :=
    Prod.ext hshuffle hface
  exact Prod.ext rfl (congrArg Prod.fst
    (Shuffle.leftBoundaryPair_injective hpair))

theorem leftInsertionToActive_injective {n : ℕ} :
    Function.Injective (@leftInsertionToActive n) := by
  rintro ⟨⟨p, q, s⟩, a⟩ ⟨⟨p', q', t⟩, b⟩ h
  have hval := congrArg Subtype.val h
  have hindex := congrArg Sigma.fst hval
  have hp : p = p' := by
    apply Fin.ext
    have hpVal := congrArg (fun i : ShihIndex (n + 1) => i.p.val) hindex
    change p.val + 1 = p'.val + 1 at hpVal
    omega
  subst p'
  have hq : q = q' := by
    apply Fin.ext
    have hqVal := congrArg (fun i : ShihIndex (n + 1) => i.q.val) hindex
    exact hqVal
  subst q'
  have hshuffle :
      Shuffle.leftBoundaryShuffle s a =
        Shuffle.leftBoundaryShuffle t b :=
    eq_of_heq (ShihIndex.mk.inj hindex).2.2
  have hfaceVal := congrArg
    (fun z : ShihUpperNonmixedData n => z.val.2.val) h
  simp only [leftInsertionToActive, ShihIndex.leftUpperLocalFaceOf,
    Fin.val_cast] at hfaceVal
  have hface :
      Shuffle.leftBoundaryIndex s a = Shuffle.leftBoundaryIndex t b :=
    Fin.ext hfaceVal
  have hpair : Shuffle.leftBoundaryPair (a, s) =
      Shuffle.leftBoundaryPair (b, t) := Prod.ext hshuffle hface
  have hz := Shuffle.leftBoundaryPair_injective hpair
  cases hz
  rfl

theorem rightInsertionToActive_injective {n : ℕ} :
    Function.Injective (@rightInsertionToActive n) := by
  rintro ⟨⟨p, q, s⟩, a⟩ ⟨⟨p', q', t⟩, b⟩ h
  have hval := congrArg Subtype.val h
  have hindex := congrArg Sigma.fst hval
  have hp : p = p' := by
    apply Fin.ext
    have hpVal := congrArg (fun i : ShihIndex (n + 1) => i.p.val) hindex
    exact hpVal
  subst p'
  have hq : q = q' := by
    apply Fin.ext
    have hqVal := congrArg (fun i : ShihIndex (n + 1) => i.q.val) hindex
    change q.val + 1 = q'.val + 1 at hqVal
    omega
  subst q'
  have hshuffle :
      Shuffle.rightBoundaryShuffle s a =
        Shuffle.rightBoundaryShuffle t b :=
    eq_of_heq (ShihIndex.mk.inj hindex).2.2
  have hfaceVal := congrArg
    (fun z : ShihUpperNonmixedData n => z.val.2.val) h
  simp only [rightInsertionToActive, ShihIndex.rightUpperLocalFaceOf,
    Fin.val_cast] at hfaceVal
  have hface :
      Shuffle.rightBoundaryIndex s a = Shuffle.rightBoundaryIndex t b :=
    Fin.ext hfaceVal
  have hpair : Shuffle.rightBoundaryPair (a, s) =
      Shuffle.rightBoundaryPair (b, t) := Prod.ext hshuffle hface
  have hz := Shuffle.rightBoundaryPair_injective hpair
  cases hz
  rfl

theorem leftEdgeToActive_isLeft {n : ℕ} (z : ShihLeftEdgeData n) :
    Shuffle.IsLeftBoundary (leftEdgeToActive z).val.1.shuffle
      (leftEdgeToActive z).val.2 := by
  rcases z with ⟨q, a⟩
  simpa only [leftEdgeToActive, ShihIndex.leftEdgeIndex,
    ShihIndex.leftEdgeLocalFace, Shuffle.leftBoundaryPair,
    Fin.cast_eq_self] using
    Shuffle.leftBoundaryPair_isLeftBoundary
      (a, Shuffle.leftUnitShuffle q.val)

theorem leftInsertionToActive_isLeft {n : ℕ}
    (z : ShihLeftInsertionData n) :
    Shuffle.IsLeftBoundary (leftInsertionToActive z).val.1.shuffle
      (leftInsertionToActive z).val.2 := by
  rcases z with ⟨i, a⟩
  simpa only [leftInsertionToActive, ShihIndex.leftUpperOf,
    ShihIndex.leftUpperLocalFaceOf, Shuffle.leftBoundaryPair,
    Fin.cast_eq_self] using
    Shuffle.leftBoundaryPair_isLeftBoundary (a, i.shuffle)

theorem rightInsertionToActive_isRight {n : ℕ}
    (z : ShihRightInsertionData n) :
    Shuffle.IsRightBoundary (rightInsertionToActive z).val.1.shuffle
      (rightInsertionToActive z).val.2 := by
  rcases z with ⟨i, b⟩
  simpa only [rightInsertionToActive, ShihIndex.rightUpperOf,
    ShihIndex.rightUpperLocalFaceOf, Shuffle.rightBoundaryPair,
    Fin.cast_eq_self] using
    Shuffle.rightBoundaryPair_isRightBoundary (b, i.shuffle)

theorem leftEdgeToActive_ne_leftInsertionToActive {n : ℕ}
    (e : ShihLeftEdgeData n) (z : ShihLeftInsertionData n) :
    leftEdgeToActive e ≠ leftInsertionToActive z := by
  intro h
  have hp := congrArg
    (fun w : ShihUpperNonmixedData n => w.val.1.p.val) h
  change 0 = z.1.p.val + 1 at hp
  omega

theorem leftEdgeToActive_ne_rightInsertionToActive {n : ℕ}
    (e : ShihLeftEdgeData n) (z : ShihRightInsertionData n) :
    leftEdgeToActive e ≠ rightInsertionToActive z := by
  intro h
  have hl := leftEdgeToActive_isLeft e
  rw [h] at hl
  exact Shuffle.isLeftBoundary_not_isRightBoundary hl
    (rightInsertionToActive_isRight z)

theorem leftInsertionToActive_ne_rightInsertionToActive {n : ℕ}
    (x : ShihLeftInsertionData n) (y : ShihRightInsertionData n) :
    leftInsertionToActive x ≠ rightInsertionToActive y := by
  intro h
  have hl := leftInsertionToActive_isLeft x
  rw [h] at hl
  exact Shuffle.isLeftBoundary_not_isRightBoundary hl
    (rightInsertionToActive_isRight y)

theorem activeBoundaryDataToNonmixed_injective {n : ℕ} :
    Function.Injective (@activeBoundaryDataToNonmixed n) := by
  intro x y h
  rcases x with e | x
  · rcases y with e' | y
    · exact congrArg Sum.inl (leftEdgeToActive_injective h)
    · rcases y with y | y
      · exact False.elim (leftEdgeToActive_ne_leftInsertionToActive e y h)
      · exact False.elim (leftEdgeToActive_ne_rightInsertionToActive e y h)
  · rcases x with x | x
    · rcases y with e | y
      · exact False.elim
          (leftEdgeToActive_ne_leftInsertionToActive e x h.symm)
      · rcases y with y | y
        · exact congrArg (fun z => Sum.inr (Sum.inl z))
            (leftInsertionToActive_injective h)
        · exact False.elim
            (leftInsertionToActive_ne_rightInsertionToActive x y h)
    · rcases y with e | y
      · exact False.elim
          (leftEdgeToActive_ne_rightInsertionToActive e x h.symm)
      · rcases y with y | y
        · exact False.elim
            (leftInsertionToActive_ne_rightInsertionToActive y x h.symm)
        · exact congrArg (fun z => Sum.inr (Sum.inr z))
            (rightInsertionToActive_injective h)

theorem activeBoundaryDataToNonmixed_bijective {n : ℕ} :
    Function.Bijective (@activeBoundaryDataToNonmixed n) :=
  ⟨activeBoundaryDataToNonmixed_injective,
    activeBoundaryDataToNonmixed_surjective⟩

noncomputable def activeBoundaryDataEquivNonmixed (n : ℕ) :
    ShihActiveBoundaryData n ≃ ShihUpperNonmixedData n :=
  Equiv.ofBijective activeBoundaryDataToNonmixed
    activeBoundaryDataToNonmixed_bijective

private noncomputable def finSuccEquivInterior (k : ℕ) :
    Fin (k + 1) ≃ {a : Fin (k + 3) // 0 < a.val ∧ a.val < k + 2} where
  toFun a := ⟨a.castSucc.succ, by simp; omega⟩
  invFun a := ⟨a.val - 1, by omega⟩
  left_inv a := by apply Fin.ext; simp
  right_inv a := by apply Subtype.ext; apply Fin.ext; simp; omega

private noncomputable def finSuccEquivPositive (k : ℕ) :
    Fin (k + 1) ≃ {a : Fin (k + 2) // 0 < a.val} where
  toFun a := ⟨a.succ, by simp⟩
  invFun a := ⟨a.val - 1, by omega⟩
  left_inv a := by apply Fin.ext; simp
  right_inv a := by apply Subtype.ext; apply Fin.ext; simp; omega

private theorem sum_fin_eq_zero_add_interior_add_last
    {A : Type*} [AddCommMonoid A] (k : ℕ) (f : Fin (k + 3) → A) :
    ∑ a, f a = f 0 +
      (∑ a : {a : Fin (k + 3) // 0 < a.val ∧ a.val < k + 2}, f a) +
      f (Fin.last (k + 2)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hmiddle := Fintype.sum_equiv (finSuccEquivInterior k)
    (fun a : Fin (k + 1) => f a.castSucc.succ)
    (fun a : {a : Fin (k + 3) // 0 < a.val ∧ a.val < k + 2} => f a)
    (fun _ => rfl)
  rw [hmiddle]
  rw [show (Fin.last (k + 1)).succ = Fin.last (k + 2) by rfl]
  exact (add_assoc _ _ _).symm

private theorem sum_fin_eq_zero_add_positive
    {A : Type*} [AddCommMonoid A] (k : ℕ) (f : Fin (k + 2) → A) :
    ∑ a, f a = f 0 + ∑ a : {a : Fin (k + 2) // 0 < a.val}, f a := by
  rw [Fin.sum_univ_succ]
  exact congrArg (f 0 + ·) (Fintype.sum_equiv (finSuccEquivPositive k)
    (fun a : Fin (k + 1) => f a.succ)
    (fun a : {a : Fin (k + 2) // 0 < a.val} => f a)
    (fun _ => rfl))

theorem sum_shihUpperNonmixedData_eq_activeBoundaryData
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihUpperActiveData n → A) :
    ∑ z : ShihUpperNonmixedData n, f z.val =
      ∑ z : ShihActiveBoundaryData n,
        f (activeBoundaryDataToNonmixed z).val := by
  symm
  exact Fintype.sum_equiv (activeBoundaryDataEquivNonmixed n)
    (fun z : ShihActiveBoundaryData n =>
      f (activeBoundaryDataToNonmixed z).val)
    (fun z : ShihUpperNonmixedData n => f z.val)
    (fun _ => rfl)

theorem sum_shihLeftInsertionData_split
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihLeftInsertionData n → A) :
    ∑ z, f z =
      (∑ i : ShihIndex n, f ⟨i, 0⟩) +
      (∑ z : ShihLowerLeftData n, f ⟨z.1, z.2.val⟩) +
      ∑ i : ShihIndex n, f ⟨i, Fin.last (i.p + 2)⟩ := by
  calc
    _ = ∑ i : ShihIndex n, ∑ a : Fin (i.p + 3), f ⟨i, a⟩ :=
      Fintype.sum_sigma' _
    _ = ∑ i : ShihIndex n,
        (f ⟨i, 0⟩ +
          (∑ a : {a : Fin (i.p + 3) // 0 < a.val ∧ a.val < i.p + 2},
            f ⟨i, a.val⟩) +
          f ⟨i, Fin.last (i.p + 2)⟩) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_fin_eq_zero_add_interior_add_last i.p (fun a => f ⟨i, a⟩)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [← Fintype.sum_sigma']
      rfl

theorem sum_shihRightInsertionData_split
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihRightInsertionData n → A) :
    ∑ z, f z =
      (∑ i : ShihIndex n, f ⟨i, 0⟩) +
      ∑ z : ShihLowerRightData n, f ⟨z.1, z.2.val⟩ := by
  calc
    _ = ∑ i : ShihIndex n, ∑ b : Fin (i.q + 2), f ⟨i, b⟩ :=
      Fintype.sum_sigma' _
    _ = ∑ i : ShihIndex n,
        (f ⟨i, 0⟩ +
          ∑ b : {b : Fin (i.q + 2) // 0 < b.val}, f ⟨i, b.val⟩) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_fin_eq_zero_add_positive i.q (fun b => f ⟨i, b⟩)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rw [← Fintype.sum_sigma']
      rfl

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- An active-data term expressed directly through its Shih index and local
active face. -/
theorem shihUpperActiveDataTerm_eq
    (X Y : SimplicialObject C) {n : ℕ} (z : ShihUpperActiveData n) :
    shihUpperActiveDataTerm X Y z =
      shihUpperBoundaryTerm X Y (n + 1) z.1
        (z.1.activeBoundaryFace z.2) := by
  rcases z with ⟨i, r⟩
  dsimp only [shihUpperActiveDataTerm, shihUpperPositiveActiveEquiv]
  congr 1
  apply Fin.ext
  change (i.gap + r.val - 1) + 1 = i.gap + r.val
  have hgap := i.gap_pos
  omega

@[simp]
theorem shihUpperActiveDataTerm_leftInsertion
    (X Y : SimplicialObject C) {n : ℕ} (z : ShihLeftInsertionData n) :
    shihUpperActiveDataTerm X Y (leftInsertionToActive z).val =
      shihUpperBoundaryTerm X Y (n + 1) (z.1.leftUpperOf z.2)
        (z.1.leftUpperFaceOf z.2) := by
  rw [shihUpperActiveDataTerm_eq]
  congr 1
  apply Fin.ext
  simp [leftInsertionToActive, ShihIndex.leftUpperLocalFaceOf,
    ShihIndex.leftUpperFaceOf, ShihIndex.activeBoundaryFace]

@[simp]
theorem shihUpperActiveDataTerm_rightInsertion
    (X Y : SimplicialObject C) {n : ℕ} (z : ShihRightInsertionData n) :
    shihUpperActiveDataTerm X Y (rightInsertionToActive z).val =
      shihUpperBoundaryTerm X Y (n + 1) (z.1.rightUpperOf z.2)
        (z.1.rightUpperFaceOf z.2) := by
  rw [shihUpperActiveDataTerm_eq]
  congr 1
  apply Fin.ext
  simp [rightInsertionToActive, ShihIndex.rightUpperLocalFaceOf,
    ShihIndex.rightUpperFaceOf, ShihIndex.activeBoundaryFace]

@[simp]
theorem shihUpperActiveDataTerm_leftEdge
    (X Y : SimplicialObject C) {n : ℕ} (z : ShihLeftEdgeData n) :
    shihUpperActiveDataTerm X Y (leftEdgeToActive z).val =
      shihUpperBoundaryTerm X Y (n + 1)
        (ShihIndex.leftEdgeIndex (n + 1) z.1 z.2)
        (ShihIndex.leftEdgeFace (n + 1) z.1 z.2) := by
  rw [shihUpperActiveDataTerm_eq]
  congr 1

theorem sum_shihLeftEdgeData_term
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihLeftEdgeData n,
      shihUpperActiveDataTerm X Y (leftEdgeToActive z).val) =
    ∑ q : Fin (n + 1),
      (shihUpperBoundaryTerm X Y (n + 1)
          (ShihIndex.leftEdgeIndex (n + 1) q 0)
          (ShihIndex.leftEdgeFace (n + 1) q 0) +
        shihUpperBoundaryTerm X Y (n + 1)
          (ShihIndex.leftEdgeIndex (n + 1) q (Fin.last 1))
          (ShihIndex.leftEdgeFace (n + 1) q (Fin.last 1))) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fin.sum_univ_two]
  rw [shihUpperActiveDataTerm_leftEdge,
    shihUpperActiveDataTerm_leftEdge]
  rw [show (1 : Fin 2) = Fin.last 1 by rfl]

theorem sum_shihLeftInsertionData_term
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihLeftInsertionData n,
      shihUpperActiveDataTerm X Y (leftInsertionToActive z).val) =
    ((∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1) (i.leftUpperOf 0)
          (i.leftUpperFaceOf 0)) +
      (∑ z : ShihLowerLeftData n,
        shihUpperBoundaryTerm X Y (n + 1) (z.1.leftUpperOf z.2)
          (z.1.leftUpperFaceOf z.2)) +
      ∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1)
          (i.leftUpperOf (Fin.last (i.p + 2)))
          (i.leftUpperFaceOf (Fin.last (i.p + 2)))) := by
  rw [sum_shihLeftInsertionData_split]
  apply congrArg₂ (fun a b => a + b)
  · apply congrArg₂ (fun a b => a + b)
    · apply Finset.sum_congr rfl
      intro i _
      exact shihUpperActiveDataTerm_leftInsertion X Y ⟨i, 0⟩
    · apply Finset.sum_congr rfl
      rintro ⟨i, a⟩ _
      exact shihUpperActiveDataTerm_leftInsertion X Y ⟨i, a.val⟩
  · apply Finset.sum_congr rfl
    intro i _
    exact shihUpperActiveDataTerm_leftInsertion X Y
      ⟨i, Fin.last (i.p + 2)⟩

theorem sum_shihRightInsertionData_term
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihRightInsertionData n,
      shihUpperActiveDataTerm X Y (rightInsertionToActive z).val) =
    ((∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1) (i.rightUpperOf 0)
          (i.rightUpperFaceOf 0)) +
      ∑ z : ShihLowerRightData n,
        shihUpperBoundaryTerm X Y (n + 1) (z.1.rightUpperOf z.2)
          (z.1.rightUpperFaceOf z.2)) := by
  rw [sum_shihRightInsertionData_split]
  apply congrArg₂ (fun a b => a + b)
  · apply Finset.sum_congr rfl
    intro i _
    exact shihUpperActiveDataTerm_rightInsertion X Y ⟨i, 0⟩
  · apply Finset.sum_congr rfl
    rintro ⟨i, b⟩ _
    exact shihUpperActiveDataTerm_rightInsertion X Y ⟨i, b.val⟩

/-- Recover the canonical mixed-face witness from global mixed active data. -/
noncomputable def ShihUpperMixedData.mixedFace {n : ℕ}
    (z : ShihUpperMixedData n) :
    Shuffle.MixedFace (z.val.1.p + 1) z.val.1.q :=
  mixedFaceOfShihUpperMixedData
    ⟨(z.val.1.shuffle, z.val.2), z.property⟩

@[simp]
theorem ShihUpperMixedData.mixedFace_shuffle {n : ℕ}
    (z : ShihUpperMixedData n) : z.mixedFace.shuffle = z.val.1.shuffle := rfl

@[simp]
theorem ShihUpperMixedData.mixedFace_faceIndex {n : ℕ}
    (z : ShihUpperMixedData n) : z.mixedFace.faceIndex = z.val.2 :=
  mixedFaceOfShihUpperMixedData_faceIndex _

/-- The global partner involution on mixed active data. -/
noncomputable def ShihUpperMixedData.partner {n : ℕ}
    (z : ShihUpperMixedData n) : ShihUpperMixedData n :=
  let x := z.mixedFace
  ⟨⟨z.val.1.replaceShuffle x.partner.shuffle, x.partner.faceIndex⟩,
    ⟨x.partner.lowerPosition, x.partner.upperPosition,
      x.partner.adjacent, rfl, x.partner.mixed⟩⟩

theorem ShihUpperMixedData.mixedFace_partner {n : ℕ}
    (z : ShihUpperMixedData n) : z.partner.mixedFace = z.mixedFace.partner := by
  apply Shuffle.MixedFace.ext
  · rfl
  · apply Fin.ext
    have hface := z.partner.mixedFace_faceIndex
    change z.partner.mixedFace.upperPosition.castSucc =
      z.mixedFace.partner.upperPosition.castSucc at hface
    have hupper := Fin.castSucc_inj.mp hface
    have hadjacent := z.partner.mixedFace.adjacent
    have hadjacentPartner := z.mixedFace.partner.adjacent
    have hupperVal := congrArg Fin.val hupper
    omega
  · apply Fin.ext
    have hface := z.partner.mixedFace_faceIndex
    change z.partner.mixedFace.upperPosition.castSucc =
      z.mixedFace.partner.upperPosition.castSucc at hface
    exact congrArg Fin.val (Fin.castSucc_inj.mp hface)

@[simp]
theorem ShihUpperMixedData.partner_partner {n : ℕ}
    (z : ShihUpperMixedData n) : z.partner.partner = z := by
  apply Subtype.ext
  apply Sigma.ext
  · rw [ShihIndex.mk.injEq]
    refine ⟨rfl, HEq.rfl, heq_of_eq ?_⟩
    change z.partner.mixedFace.partner.shuffle = z.mixedFace.shuffle
    rw [z.mixedFace_partner]
    exact congrArg Shuffle.MixedFace.shuffle z.mixedFace.partner_partner
  · apply heq_of_eq
    change z.partner.mixedFace.partner.faceIndex = z.val.2
    rw [z.mixedFace_partner]
    have hface :
        z.mixedFace.partner.partner.faceIndex = z.mixedFace.faceIndex :=
      congrArg Shuffle.MixedFace.faceIndex z.mixedFace.partner_partner
    exact hface.trans z.mixedFace_faceIndex

theorem ShihUpperMixedData.partner_ne {n : ℕ}
    (z : ShihUpperMixedData n) : z.partner ≠ z := by
  intro h
  have hindex := congrArg (fun y : ShihUpperMixedData n => y.val.1) h
  have hshuffleHEq := (ShihIndex.mk.inj hindex).2.2
  have hshuffle : z.mixedFace.partner.shuffle = z.mixedFace.shuffle :=
    eq_of_heq hshuffleHEq
  apply z.mixedFace.partner_ne
  apply (shihMixedFaceEquivUpperMixedData
    (z.val.1.p : ℕ) (z.val.1.q : ℕ)).injective
  apply Subtype.ext
  apply Prod.ext
  · exact hshuffle
  · exact z.mixedFace.partner_faceIndex

/-- The global mixed active sum cancels without a bidegree specialization. -/
theorem shihUpperMixedData_sum_eq_zero_global
    (X Y : SimplicialObject C) (n : ℕ) :
    ∑ z : ShihUpperMixedData n,
      shihUpperActiveDataTerm X Y z.val = 0 := by
  apply Finset.sum_involution (fun z _ => z.partner)
  · intro z _
    rw [shihUpperActiveDataTerm_eq, shihUpperActiveDataTerm_eq]
    simpa only [ShihUpperMixedData.partner,
      ShihUpperMixedData.mixedFace_faceIndex,
      ShihIndex.activeBoundaryFace, ShihIndex.replaceShuffle,
      ShihIndex.gap] using
      shihMixedActiveBoundaryTerm_add_partner_eq_zero
        X Y z.val.1 z.mixedFace rfl
  · intro z _ _
    exact z.partner_ne
  · intro z _
    exact z.partner_partner
  · intro z _
    simp

/-- The active upper stratum is exactly the exceptional left edge together
with the ordinary left- and right-insertion families. -/
theorem shihActiveUpperReindexIdentity
    (X Y : SimplicialObject C) (n : ℕ) :
    ShihActiveUpperReindexIdentity X Y n := by
  rw [ShihActiveUpperReindexIdentity]
  change (∑ z : ShihUpperActiveData n,
    shihUpperActiveDataTerm X Y z) = _
  rw [shihUpperActiveData_sum_eq_mixed_add_nonmixed,
    shihUpperMixedData_sum_eq_zero_global, zero_add,
    sum_shihUpperNonmixedData_eq_activeBoundaryData]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  change
    (∑ z : ShihLeftEdgeData n,
      shihUpperActiveDataTerm X Y (leftEdgeToActive z).val) +
      ((∑ z : ShihLeftInsertionData n,
          shihUpperActiveDataTerm X Y (leftInsertionToActive z).val) +
        ∑ z : ShihRightInsertionData n,
          shihUpperActiveDataTerm X Y (rightInsertionToActive z).val) = _
  rw [sum_shihLeftEdgeData_term,
    sum_shihLeftInsertionData_term,
    sum_shihRightInsertionData_term]
  abel

end AlgebraicTopology.EilenbergZilber
