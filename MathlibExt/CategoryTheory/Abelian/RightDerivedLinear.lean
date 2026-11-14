/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Homology/DerivedLinear.lean.
The source has no individual copyright or author notice and is licensed
under Apache 2.0. Modification notice: move the completed proofs to
CategoryTheory.DerivedLinear in a standalone MathlibExt module, with no
Stacks import, axiom or unresolved request.
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# The right derived functors of a linear functor are linear

Let `R` be a commutative ring and let `D` and `E` be `R`-linear abelian categories, `D` with
enough injectives. The right derived functors of an `R`-linear additive functor `G : D ⥤ E` are
again `R`-linear: a scalar acts on `RⁿG(X)` as the image under `RⁿG` of multiplication by that
scalar on `X`.

## Main results

* `CategoryTheory.DerivedLinear.homologyFunctor_linear`: homology is linear.
* `CategoryTheory.DerivedLinear.rightDerived_linear`: right derived functors are linear.
* `CategoryTheory.DerivedLinear.injectiveResolutions_additive`: resolutions are additive.
* `CategoryTheory.DerivedLinear.rightDerived_additive`: right derived functors are additive.

## Implementation notes

`CategoryTheory.Functor.rightDerived` is the composite of the injective-resolution functor into
the homotopy category, the degreewise image under `G`, and the degree-`n` homology of a complex
in the homotopy category, so linearity of each of the three factors gives linearity of the
composite. The middle factor is linear by Mathlib's
`CategoryTheory.Functor.mapHomologicalComplex_linear`; the other two are the auxiliary
statements of this module.

Linearity of the homology of a complex is read off from linearity of the short complex in each
degree, and linearity of the injective-resolution functor from the homotopy between the
descent of multiplication by a scalar along an injective resolution and that scalar acting on
the resolution.

`Mathlib` has `CategoryTheory.Functor.Linear` for `CategoryTheory.ShortComplex.homologyFunctor`
and for `CategoryTheory.Functor.mapHomologicalComplex`, but not for
`CategoryTheory.HomologicalComplex.homologyFunctor`; that is `homologyFunctor_linear` below.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DerivedLinear

variable {R : Type*} [CommRing R] {D E : Type*} [Category* D] [Category* E]
  [Abelian D] [Abelian E] [Linear R D] [Linear R E]

/-- Two maps of injective resolutions lifting `f` have the same image in the homotopy category. -/
private theorem quotient_map_desc_eq [EnoughInjectives D] {X Y : D} (f : X ⟶ Y)
    (I : InjectiveResolution Y) (J : InjectiveResolution X) (φ : J.cocomplex ⟶ I.cocomplex)
    (h : J.ι ≫ φ = (CochainComplex.single₀ D).map f ≫ I.ι) :
    (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map (InjectiveResolution.desc f I J) =
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map φ :=
  HomotopyCategory.eq_of_homotopy _ _
    (InjectiveResolution.descHomotopy f _ _ (InjectiveResolution.desc_commutes f I J) h)

/-- **The injective-resolution functor into the homotopy category is additive.**  The descent of
`f + g` along injective resolutions is homotopic to the sum of the descents, because both lift
`f + g`; so the two become equal in the homotopy category. -/
theorem injectiveResolutions_additive [EnoughInjectives D] :
    (injectiveResolutions D).Additive where
  map_add {Xo Yo} f g := by
    let I := injectiveResolution Xo
    let J := injectiveResolution Yo
    let Q := HomotopyCategory.quotient D (ComplexShape.up ℕ)
    dsimp only [injectiveResolutions]
    change Q.map (InjectiveResolution.desc (f + g) J I) =
      Q.map (InjectiveResolution.desc f J I) + Q.map (InjectiveResolution.desc g J I)
    rw [← Q.map_add]
    refine quotient_map_desc_eq _ _ _ _ ?_
    rw [Preadditive.comp_add, InjectiveResolution.desc_commutes f J I,
      InjectiveResolution.desc_commutes g J I, Functor.map_add, Preadditive.add_comp]

/-- **The right derived functors of an additive functor are additive.**  Each of the three factors
of `CategoryTheory.Functor.rightDerived` is: the injective-resolution functor by
`injectiveResolutions_additive`, and the other two by Mathlib instances. -/
theorem rightDerived_additive [EnoughInjectives D] (G : D ⥤ E) [G.Additive] (n : ℕ) :
    (G.rightDerived n).Additive := by
  let : (injectiveResolutions D).Additive := injectiveResolutions_additive
  change Functor.Additive
    (injectiveResolutions D ⋙ G.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
      HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) n)
  infer_instance

private theorem injectiveResolutions_linear [EnoughInjectives D] :
    Functor.Linear R (injectiveResolutions D) := by
  rw [Functor.linear_iff]
  intro X a
  let I := injectiveResolution X
  let Q := HomotopyCategory.quotient D (ComplexShape.up ℕ)
  let : Functor.Linear R (CochainComplex.single₀ D) := by
    rw [Functor.linear_iff]
    intro Y s
    ext
    simp only [CochainComplex.single₀_map_f_zero, CochainComplex.single₀_obj_zero,
      HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    rfl
  dsimp only [injectiveResolutions]
  change Q.map (InjectiveResolution.desc (a • 𝟙 X) I I) = a • 𝟙 (Q.obj I.cocomplex)
  refine (quotient_map_desc_eq _ _ _ (a • 𝟙 I.cocomplex) ?_).trans ?_
  · calc
      I.ι ≫ (a • 𝟙 I.cocomplex) = a • I.ι := by simp
      _ = (CochainComplex.single₀ D).map (a • 𝟙 X) ≫ I.ι := by
        rw [Functor.map_smul]
        simp [Linear.smul_comp]
  · simp [Q]

/-- **The degree-`n` homology of a cochain complex is an `R`-linear functor.**  A scalar acts on
the homology as the image of its action on the complex, because it acts that way on the short
complex in degree `n`. -/
theorem homologyFunctor_linear (n : ℕ) :
    Functor.Linear R (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n) := by
  let : Functor.Linear R
      (HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℕ) n) :=
    { map_smul := by intros; ext <;> rfl }
  exact Functor.linear_of_iso R
    (HomologicalComplex.homologyFunctorIso D (ComplexShape.up ℕ) n).symm

private theorem homotopyCategory_homology_linear (n : ℕ) :
    Functor.Linear R (HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n) := by
  let Q := HomotopyCategory.quotient D (ComplexShape.up ℕ)
  let : Functor.Linear R (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n) :=
    homologyFunctor_linear n
  let : Functor.Linear R (Q ⋙ HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n) :=
    Functor.linear_of_iso R
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).symm
  exact Functor.linear_of_full_essSurj_comp Q _

/-- The right derived functors of a linear functor are linear. -/
theorem rightDerived_linear [EnoughInjectives D] (G : D ⥤ E) [G.Additive]
    [Functor.Linear R G] (n : ℕ) : Functor.Linear R (G.rightDerived n) := by
  let : Functor.Linear R (injectiveResolutions D) := injectiveResolutions_linear
  let : Functor.Linear R (HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) n) :=
    homotopyCategory_homology_linear n
  change Functor.Linear R
    (injectiveResolutions D ⋙ G.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
      HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) n)
  infer_instance

end CategoryTheory.DerivedLinear

end
