/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IntegerSchemeChow

/-!
# Signed integral cycles and the Chow quotient

Negative dimensions support no points, so their cycle groups are trivial.
`dimensionPart` is the identity on cycles of its dimension. On the point
`Spec k` every cycle has dimension zero, none has dimension one, and there are
no rational equivalences, so the degree-zero Chow class map is injective.
Principal relations die in the Chow group, so a degree comparison forces
principal zero-cycles to have degree zero.
-/

noncomputable section

namespace MathlibExtTest.IntegerSchemeChow

open CategoryTheory AlgebraicGeometry.IntegerSchemeChow
open AlgebraicGeometry (Scheme Spec AlgebraicCycle)

/-! ## Signed dimensions and the dimension projection -/

section Generic

variable (X : Scheme.{0})

theorem not_pointDimension_of_neg (x : X) {d : ℤ} (hd : d < 0) : ¬ PointDimension X x d := by
  rintro ⟨n, hn, -⟩
  omega

theorem eq_zero_of_mem_neg {d : ℤ} (hd : d < 0) (c : AlgebraicCycle X ℤ)
    (hc : c ∈ cyclesOfDimension X d) : c = 0 := by
  ext x
  by_contra h
  exact not_pointDimension_of_neg X x hd (hc x h)

example (c : CycleGroup X (-1)) : c = 0 :=
  Subtype.ext (eq_zero_of_mem_neg X (by norm_num) c.val c.2)

theorem dimensionPart_apply_of (d : ℤ) (c : AlgebraicCycle X ℤ) (x : X)
    (h : PointDimension X x d) : (dimensionPart X d c).val x = c x := by
  simp [dimensionPart, h]

theorem dimensionPart_apply_of_not (d : ℤ) (c : AlgebraicCycle X ℤ) (x : X)
    (h : ¬ PointDimension X x d) : (dimensionPart X d c).val x = 0 := by
  simp [dimensionPart, h]

/-- The dimension projection is the identity on cycles of that dimension. -/
example (d : ℤ) (c : CycleGroup X d) : dimensionPart X d c.val = c := by
  apply Subtype.ext
  ext x
  by_cases h : PointDimension X x d
  · rw [dimensionPart_apply_of X d _ x h]
  · rw [dimensionPart_apply_of_not X d _ x h]
    by_contra hc
    exact h (c.2 x (Ne.symm hc))

end Generic

/-! ## The point `Spec k` -/

section Point

variable (k : Type) [Field k]

/-- `Spec k` over itself. -/
def point : FieldScheme k where
  scheme := Over.mk (𝟙 (Spec (.of k)))
  finiteType := inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType (𝟙 (Spec (.of k))))
  quasiCompact := inferInstanceAs (AlgebraicGeometry.QuasiCompact (𝟙 (Spec (.of k))))
  noetherian := inferInstanceAs (AlgebraicGeometry.IsNoetherian (Spec (.of k)))

theorem pointDimension_zero (x : Spec (.of k)) : PointDimension (Spec (.of k)) x 0 :=
  ⟨0, rfl, Order.height_eq_zero.mpr fun y _ => (Subsingleton.elim x y).le⟩

example : cyclesOfDimension (point k).scheme.left 0 = ⊤ := by
  ext c
  simp only [AddSubgroup.mem_top, iff_true]
  exact fun x _ => pointDimension_zero k x

theorem not_pointDimension_one (x : Spec (.of k)) : ¬ PointDimension (Spec (.of k)) x 1 := by
  rintro ⟨n, hn, hh⟩
  rw [Order.height_eq_zero.mpr fun y _ => (Subsingleton.elim x y).le] at hh
  have hn0 : n = 0 := by exact_mod_cast hh.symm
  omega

example : cyclesOfDimension (point k).scheme.left 1 = ⊥ := by
  ext c
  simp only [AddSubgroup.mem_bot]
  constructor
  · intro hc
    ext x
    by_contra h
    exact not_pointDimension_one k x (hc x h)
  · rintro rfl
    exact zero_mem _

/-- A point has no closed integral subscheme of positive dimension. -/
theorem no_closedIntegralScheme_pos {d : ℤ} (hd : 0 < d)
    (W : ClosedIntegralScheme (point k).scheme.left d) : False := by
  have hinj : Function.Injective W.inclusion :=
    (W.inclusion.isClosedEmbedding).injective
  have : Subsingleton W.scheme := ⟨fun a b => hinj (Subsingleton.elim (α := Spec (.of k)) _ _)⟩
  have : DiscreteTopology W.scheme := inferInstance
  have h0 := topologicalKrullDim_zero_of_discreteTopology W.scheme
  rw [W.krullDimension_eq] at h0
  have hdim : W.dimension ≤ 0 := by exact_mod_cast h0
  have := W.dimension_eq
  omega

/-- The point has no rational equivalences in degree zero, so `CH₀(Spec k)` is
the full cycle group: the Chow quotient is not degenerate. -/
theorem rationalEquivalences_point : rationalEquivalences (point k).scheme.left 0 = ⊥ := by
  rw [rationalEquivalences, AddSubgroup.closure_eq_bot_iff]
  rintro c ⟨W, -, -, -⟩
  exact (no_closedIntegralScheme_pos k (by norm_num) W).elim

example : Function.Injective (cycleClass (point k) 0) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  have h := (QuotientAddGroup.eq_zero_iff c).mp hc
  rwa [rationalEquivalences_point, AddSubgroup.mem_bot] at h

end Point

/-! ## The Chow quotient -/

section Chow

variable {k : Type} [Field k] (X : FieldScheme k)

example (d : ℤ) : Function.Surjective (cycleClass X d) := QuotientAddGroup.mk'_surjective _

theorem cycleClass_eq_zero_of_principal (d : ℤ) (c : CycleGroup X.scheme.left d)
    (hc : IsPrincipalRelation X.scheme.left d c) : cycleClass X d c = 0 :=
  (QuotientAddGroup.eq_zero_iff c).mpr (AddSubgroup.subset_closure hc)

example (c : CycleGroup X.scheme.left (-1)) : cycleClass X (-1) c = 0 := by
  have hc : c = 0 := Subtype.ext (eq_zero_of_mem_neg X.scheme.left (by norm_num) c.val c.2)
  rw [hc, map_zero]

/-- A degree comparison forces principal zero-cycles to have degree zero. -/
example [AlgebraicGeometry.IsProper X.scheme.hom] (D : DegreeComparison X)
    (c : CycleGroup X.scheme.left 0) (hc : IsPrincipalRelation X.scheme.left 0 c) :
    AlgebraicCycle.degree X.scheme.hom c.val = 0 := by
  rw [← D.normalized c, cycleClass_eq_zero_of_principal X 0 c hc, map_zero]

end Chow

end MathlibExtTest.IntegerSchemeChow
