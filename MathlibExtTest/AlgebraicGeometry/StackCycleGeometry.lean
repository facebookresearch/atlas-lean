/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.StackCycleGeometry

/-!
# Integral stack cycles and scheme fundamental cycles

Signed atlas dimensions can be negative, with no natural-number truncation.
Closed cuts contain the image of their realization and the universal point of
their representing closed subscheme. Cycle generators are nonzero and
distinct. The integral fundamental cycle of an integral Noetherian scheme is
its generic point with multiplicity one.
-/

noncomputable section

namespace MathlibExtTest.StackCycleGeometry

open CategoryTheory AlgebraicGeometry.StackCycleGeometry
open AlgebraicGeometry (Scheme IsClosedImmersion IsIntegral IsNoetherian AlgebraicCycle)

variable {S : Scheme.{0}} {X : Stack S}

/-! ## Signed dimensions -/

example (a : IntegralAtlas X) : a.signedDimension = a.schemeDimension - a.relativeRank := rfl

/-- A zero-dimensional chart of relative rank two has signed dimension `-2`. -/
example (a : IntegralAtlas X) (h0 : a.schemeDimension = 0) (h1 : a.relativeRank = 2) :
    a.signedDimension = -2 := by
  simp [IntegralAtlas.signedDimension, h0, h1]

example (a : IntegralAtlas X) : HasIntegralDimension X a.signedDimension := ⟨a, rfl⟩

/-! ## Closed cuts -/

example (Z : ClosedSubstack X) (T : Over S) (x : X.Fibre T) :
    IsClosedImmersion (Z.fibre T x).hom := inferInstance

/-- The image of the realization lies in the cut. -/
example (Z : ClosedSubstack X) (T : Over S) (y : Z.source.Fibre T) :
    Z.predicate T ((component Z.inclusion T).obj y) :=
  (Z.inclusion_image T _).mpr ⟨y, ⟨Iso.refl _⟩⟩

/-- The restriction of a point to its representing closed subscheme lies in the cut. -/
example (Z : ClosedSubstack X) (T : Over S) (x : X.Fibre T) :
    Z.predicate (Over.mk ((Z.fibre T x).hom ≫ T.hom))
      ((pull X (Over.homMk (Z.fibre T x).hom :
        Over.mk ((Z.fibre T x).hom ≫ T.hom) ⟶ T)).obj x) :=
  (Z.fibre_normalized T x _ _).mpr ⟨𝟙 _, by simp⟩

/-- The cut is stable under pullback along any scheme map over `S`. -/
example (Z : ClosedSubstack X) {T V : Over S} (a : V ⟶ T) (x : X.Fibre T)
    (hx : Z.predicate T x) : Z.predicate V ((pull X a).obj x) :=
  Z.pull_mem a x hx

/-! ## Cycles -/

example {d : ℤ} (Z : IntegralClosedSubstack X d) : cycleClass Z ≠ 0 :=
  FreeAbelianGroup.of_ne_zero Z

example {d : ℤ} : Function.Injective (cycleClass (X := X) (d := d)) :=
  FreeAbelianGroup.of_injective

example (F : RationalUnitFamily X) (a b : IntegralAtlas X) (f : ChartArrow a b) :
    (chartFieldPull f).hom (F.value b : ChartField b) = (F.value a : ChartField a) :=
  F.naturality a b f

example (U : Scheme.{0}) [IsIntegral U] [IsNoetherian U] (f : U.functionField)
    (D : PrincipalSchemeCycle U f) (x : U) : D.val x = U.ord f x := D.2 x

/-! ## Fundamental cycles of integral schemes -/

section Fundamental

variable (U : Scheme.{0}) [IsIntegral U] [IsNoetherian U]

/-- An integral scheme has the single irreducible component `univ`. -/
@[instance_reducible]
def uniqueComponent : Unique (irreducibleComponents U) where
  default := ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  uniq Z := Subtype.ext (Set.mem_singleton_iff.mp
    (show (Z : Set U) ∈ ({Set.univ} : Set (Set U)) from
      irreducibleComponents_eq_singleton (X := U) ▸ Z.2))

theorem integralFundamentalCycle_genericPoint :
    integralFundamentalCycle U (genericPoint U) = 1 := by
  classical
  let := uniqueComponent U
  simp only [integralFundamentalCycle, Fintype.sum_unique]
  have hp : (default : irreducibleComponents U).2.1.genericPoint = genericPoint U := rfl
  rw [hp, Function.locallyFinsuppWithin.single_apply]
  simp

theorem integralFundamentalCycle_of_ne (x : U) (hx : x ≠ genericPoint U) :
    integralFundamentalCycle U x = 0 := by
  classical
  let := uniqueComponent U
  simp only [integralFundamentalCycle, Fintype.sum_unique]
  have hp : (default : irreducibleComponents U).2.1.genericPoint = genericPoint U := rfl
  rw [hp, Function.locallyFinsuppWithin.single_apply]
  simp [hx]

end Fundamental

end MathlibExtTest.StackCycleGeometry
