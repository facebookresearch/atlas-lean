/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ZeroObject
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.HarderNarasimhanFiltration

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

namespace HarderNarasimhanFiltrationTest

/-- Being a vector bundle of rank `r` is invariant under isomorphism. -/
theorem isVectorBundle_of_iso {E E' : X.Modules} (e : E ≅ E') {r : ℕ}
    (h : IsVectorBundle E r) : IsVectorBundle E' r := fun x ↦ by
  obtain ⟨U, hx, ⟨e'⟩⟩ := h x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ e'⟩⟩

/-- A zero sheaf is a vector bundle of rank zero. -/
theorem isVectorBundle_zero {Z : X.Modules} (hZ : IsZero Z) : IsVectorBundle Z 0 :=
  fun _ ↦ ⟨⊤, trivial, ⟨IsZero.iso (Functor.map_isZero _ hZ)
    ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun i ↦ i.elim0))⟩⟩

/-- Isomorphic sheaves have the same cohomology dimensions. -/
theorem finrank_cohomology_congr (f : X ⟶ Spec (.of k)) {E E' : X.Modules} (e : E ≅ E')
    (n : ℕ) : Module.finrank k (cohomology f E n) = Module.finrank k (cohomology f E' n) :=
  (((sectionsFunctor f).rightDerived n).mapIso e).toLinearEquiv.finrank_eq

/-- The slope is invariant under isomorphism. -/
theorem slope_congr (f : X ⟶ Spec (.of k)) [IsProperCurve f] {E E' : X.Modules} (e : E ≅ E')
    {r : ℕ} (hE : IsVectorBundle E r) (hE' : IsVectorBundle E' r) (hr : 0 < r) :
    slope f E r hE hr = slope f E' r hE' hr := by
  simp only [slope, bundleDegree, finrank_cohomology_congr f e]

/-- Semistability is invariant under isomorphism. -/
theorem isSemistable_of_iso (f : X ⟶ Spec (.of k)) [IsProperCurve f] [SmoothOfRelativeDimension 1 f]
    [IsIntegral X] {E E' : X.Modules}
    (e : E ≅ E') {r : ℕ} (hE : IsVectorBundle E r) (hE' : IsVectorBundle E' r) (hr : 0 < r)
    (h : IsSemistable f E r hE hr) : IsSemistable f E' r hE' hr := by
  intro s hs hsr F i hi hF hQ
  rw [← slope_congr f e hE hE' hr]
  exact h s hs hsr F (i ≫ e.inv) inferInstance hF
    (isVectorBundle_of_iso (cokernelCompIsIso i e.inv).symm hQ)

/-- The one-step Harder–Narasimhan filtration `0 ⊂ E` of a semistable bundle `E`. It
exercises the endpoint indexing (`bundle 0 = 0`, `bundle (Fin.last 1) = E`), the rank of
the only graded piece (`r - 0`, through `cokernel (0 : 0 ⟶ E) ≅ E`), and the vacuous slope
ordering of a single graded piece. -/
noncomputable def oneStep (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    (E : X.Modules) (r : ℕ)
    (hE : IsVectorBundle E r) (hr : 0 < r) (h : IsSemistable f E r hE hr) :
    Filtration f E r where
  steps := 1
  bundle := ![0, E]
  rank := ![0, r]
  zero := isZero_zero _
  rank_zero := rfl
  final := Iso.refl _
  rank_final := rfl
  locallyFree := Fin.cases (isVectorBundle_zero (isZero_zero _)) fun j ↦ by
    rw [Subsingleton.elim j 0]
    exact hE
  inclusion := fun _ ↦ 0
  monic := fun j ↦ by
    rw [Subsingleton.elim j 0]
    exact ⟨fun g h _ ↦ (isZero_zero _).eq_of_tgt g h⟩
  rank_increases := fun j ↦ by
    rw [Subsingleton.elim j 0]
    exact hr
  quotientLocallyFree := fun j ↦ by
    rw [Subsingleton.elim j 0]
    exact isVectorBundle_of_iso (cokernelZeroIsoTarget (X := 0) (Y := E)).symm hE
  semistable := fun j ↦ by
    rw [Subsingleton.elim j 0]
    exact isSemistable_of_iso f (cokernelZeroIsoTarget (X := 0) (Y := E)).symm hE _ hr h
  slope_decreases := fun i j hij ↦ absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl j)

/-- A semistable bundle has a Harder–Narasimhan filtration: the structure is inhabited. -/
example (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] (E : X.Modules)
    (r : ℕ) (hE : IsVectorBundle E r) (hr : 0 < r) (h : IsSemistable f E r hE hr) :
    Nonempty (Filtration f E r) :=
  ⟨oneStep f E r hE hr h⟩

-- The one-step filtration has a single graded piece, of the full rank.
example (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] (E : X.Modules)
    (r : ℕ) (hE : IsVectorBundle E r) (hr : 0 < r) (h : IsSemistable f E r hE hr) :
    (oneStep f E r hE hr h).steps = 1 ∧
      (oneStep f E r hE hr h).rank (Fin.last _) - (oneStep f E r hE hr h).rank 0 = r :=
  ⟨rfl, by simp [oneStep]⟩

/-- The filtration `0 ≅ E` with no steps of a zero sheaf, of rank zero. -/
noncomputable def zeroStep (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    (E : X.Modules) (hE : IsZero E) : Filtration f E 0 where
  steps := 0
  bundle := fun _ ↦ E
  rank := fun _ ↦ 0
  zero := hE
  rank_zero := rfl
  final := Iso.refl _
  rank_final := rfl
  locallyFree := fun _ ↦ isVectorBundle_zero hE
  inclusion := fun j ↦ j.elim0
  monic := fun j ↦ j.elim0
  rank_increases := fun j ↦ j.elim0
  quotientLocallyFree := fun j ↦ j.elim0
  semistable := fun j ↦ j.elim0
  slope_decreases := fun i ↦ i.elim0

/-- Every vector bundle of rank zero has a Harder–Narasimhan filtration, since it is zero: the
existence request holds in rank zero. -/
example (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] (E : X.Modules) (hE : IsVectorBundle E 0) :
    Nonempty (Filtration f E 0) :=
  ⟨zeroStep f E (isZero_of_isVectorBundle_zero hE)⟩

/-- A filtration of a bundle of positive rank has at least one step. -/
theorem steps_pos (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    {E : X.Modules} {r : ℕ}
    (F : Filtration f E r) (hr : 0 < r) : 0 < F.steps := by
  refine Nat.pos_of_ne_zero fun h ↦ hr.ne' ?_
  have e : (Fin.last F.steps : Fin (F.steps + 1)) = 0 := Fin.ext (by simp [h])
  rw [← F.rank_final, e, F.rank_zero]

/-- A filtration with at least one step is of a bundle of positive rank: the ranks start at
`0` and strictly increase up to `r`. -/
theorem rank_pos (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    {E : X.Modules} {r : ℕ}
    (F : Filtration f E r) (hpos : 0 < F.steps) : 0 < r := by
  have key : ∀ m (hm : m < F.steps), 0 < F.rank ⟨m + 1, Nat.succ_lt_succ hm⟩ := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h := F.rank_increases ⟨0, hm⟩
      have h0 : (Fin.castSucc ⟨0, hm⟩ : Fin (F.steps + 1)) = 0 := Fin.ext rfl
      rw [h0, F.rank_zero] at h
      exact h
    | succ m ih =>
      intro hm
      exact (ih (Nat.lt_of_succ_lt hm)).trans (F.rank_increases ⟨m + 1, hm⟩)
  have h := key (F.steps - 1) (Nat.sub_lt hpos one_pos)
  have e : (⟨F.steps - 1 + 1, Nat.succ_lt_succ (Nat.sub_lt hpos one_pos)⟩ :
      Fin (F.steps + 1)) = Fin.last F.steps := Fin.ext (by simp only [Fin.val_last]; omega)
  rw [e, F.rank_final] at h
  exact h

/-- The slope of the `j`-th graded piece `Eⱼ₊₁ / Eⱼ` of a filtration. -/
noncomputable def quotientSlope (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f]
    [IsIntegral X] {E : X.Modules} {r : ℕ} (F : Filtration f E r) (j : Fin F.steps) : ℚ :=
  slope f (cokernel (F.inclusion j)) (F.rank j.succ - F.rank j.castSucc)
    (F.quotientLocallyFree j) (Nat.sub_pos_of_lt (F.rank_increases j))

-- Orientation of the slope condition: in a two-step filtration the second graded piece has
-- strictly smaller slope than the first (this fails if the inequality is reversed).
example (f : X ⟶ Spec (.of k)) [IsProperCurve f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {E : X.Modules}
    {r : ℕ} (F : Filtration f E r) (h2 : F.steps = 2) :
    quotientSlope f F ⟨1, by omega⟩ < quotientSlope f F ⟨0, by omega⟩ :=
  F.slope_decreases ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.mk_lt_mk.2 one_pos)

end HarderNarasimhanFiltrationTest
