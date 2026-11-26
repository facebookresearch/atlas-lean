/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Spectra/SmashPow.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Smash.Power
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.SymmetricSequence
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Monoid

/-!
# The commutative monoid of smash powers

For a pointed simplicial set `X`, the symmetric sequence `n ↦ X^∧n` of smash powers, with
`Σ_n` permuting the smash factors and block concatenation `X^∧p ∧ X^∧q ≅ X^∧(p+q)`, is a
commutative monoid for the Day convolution product (`SymmetricSequence.smashPow X`). This is
Hovey's symmetric algebra `Sym(X)`, the free commutative monoid on `X` placed in level one, whose
modules are the symmetric spectra based on `X`. A based map `X ⟶ Y` applied in every coordinate is
a morphism of these monoids.

## Main definitions

* `SymmetricSequence.smashPow X`: the commutative monoid `n ↦ X^∧n` of smash powers. Its
  commutative monoid structure is the instance `DayFunctor.monObj`, with commutativity
  `DayFunctor.isCommMonObj`.
* `SymmetricSequence.smashPowMap f`: the morphism of monoids induced by a based map `f`.
* `SymmetricSequence.smashPowMapIso e`: the isomorphism of monoids induced by an isomorphism `e`.

## Main statements

* `SymmetricSequence.smashPow_mul_app_smashMk`: the multiplication of the smash powers
  concatenates coordinates.

## References

* M. Hovey, *Spectra and symmetric spectra in general model categories*, J. Pure Appl. Algebra
  165 (2001), 63–127.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource

open scoped DayFunctor

namespace SymmetricSequence

/-- The symmetric sequence `n ↦ X^∧n` of smash powers of a pointed simplicial set, with `Σ_n`
permuting the smash factors. Block concatenation `X^∧p ∧ X^∧q ≅ X^∧(p+q)` and `S⁰ ≅ X^∧0` make it
a commutative monoid for the Day convolution product, through the instances
`DayFunctor.monObj` and `DayFunctor.isCommMonObj`. -/
-- An abbreviation, so that the instances for lax braided functors apply to it.
noncomputable abbrev smashPow (X : PointedSSet.{u}) : SymmetricSequence.{u} :=
  .mk (PointedSSet.smashPowFunctor X)

/- The symmetric sequence of smash powers is a commutative monoid. -/
noncomputable example (X : PointedSSet.{u}) : IsCommMonObj (smashPow X) := inferInstance

/-- The multiplication `X^∧k ∧ X^∧l → X^∧(k+l)` of the monoid of smash powers, restricted along
the Day convolution unit, concatenates families of simplices. -/
lemma smashPow_mul_app_smashMk {X : PointedSSet.{u}} {k l : FiniteBijection}
    {n : SimplexCategoryᵒᵖ} (x : Fin k.len → X.right.obj n) (y : Fin l.len → X.right.obj n) :
    ((DayFunctor.η (smashPow X) (smashPow X)).app (k, l) ≫
        (MonObj.mul : smashPow X ⊗ smashPow X ⟶ smashPow X).natTrans.app (k ⊗ l)).right.app n
        (PointedSSet.smashMk (PointedSSet.smashPowMk x) (PointedSSet.smashPowMk y)) =
      PointedSSet.smashPowMk (ι := Fin (k ⊗ l).len) (Fin.append x y) := by
  rw [DayFunctor.η_app_comp_mul_natTrans_app]
  exact PointedSSet.smashPowFunctor_μ_app_smashMk x y

variable {X Y Z : PointedSSet.{u}}

/-- The morphism `X^∧n ⟶ Y^∧n` of symmetric sequences of smash powers induced by a based map
`f : X ⟶ Y`, applying `f` in every coordinate. It is a morphism of monoids, through the instance
`DayFunctor.isMonHom`. -/
noncomputable def smashPowMap (f : X ⟶ Y) : smashPow X ⟶ smashPow Y :=
  .mk (PointedSSet.smashPowFunctorMap f)

@[simp]
lemma smashPowMap_natTrans (f : X ⟶ Y) :
    (smashPowMap f).natTrans = PointedSSet.smashPowFunctorMap f := (rfl)

/-- Applying a based map in every coordinate is a monoidal natural transformation. -/
instance (f : X ⟶ Y) : NatTrans.IsMonoidal (smashPowMap f).natTrans :=
  inferInstanceAs (NatTrans.IsMonoidal (PointedSSet.smashPowFunctorMap f))

/- Applying a based map in every coordinate is a morphism of monoids of smash powers. -/
example (f : X ⟶ Y) : IsMonHom (smashPowMap f) := inferInstance

@[simp]
lemma smashPowMap_id : smashPowMap (𝟙 X) = 𝟙 _ := by
  ext1
  ext k
  simp

@[simp]
lemma smashPowMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    smashPowMap (f ≫ g) = smashPowMap f ≫ smashPowMap g := by
  ext1
  ext k
  simp

/-- The isomorphism of monoids of smash powers induced by an isomorphism `e : X ≅ Y`. -/
noncomputable def smashPowMapIso (e : X ≅ Y) : smashPow X ≅ smashPow Y where
  hom := smashPowMap e.hom
  inv := smashPowMap e.inv
  hom_inv_id := by rw [← smashPowMap_comp, e.hom_inv_id, smashPowMap_id]
  inv_hom_id := by rw [← smashPowMap_comp, e.inv_hom_id, smashPowMap_id]

@[simp]
lemma smashPowMapIso_hom (e : X ≅ Y) : (smashPowMapIso e).hom = smashPowMap e.hom := (rfl)

@[simp]
lemma smashPowMapIso_inv (e : X ≅ Y) : (smashPowMapIso e).inv = smashPowMap e.inv := (rfl)

/-- The isomorphism of smash powers induced by an isomorphism is an isomorphism of monoids. -/
instance (e : X ≅ Y) : IsMonHom (smashPowMapIso e).hom :=
  inferInstanceAs (IsMonHom (smashPowMap e.hom))

end SymmetricSequence

end MathlibExt.SpectraSource
