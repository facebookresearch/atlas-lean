/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Reduced

/-!
# Pointed reduced integral H₀ and original path components

The original reduced homology object is the kernel of the original augmentation.
Its vanishing makes the augmentation monic. The canonical H₀ component Iso
then makes the fold on integral component summands monic. A component projection
distinguishes two unequal original path components, contradicting monicity.
The supplied point gives nonemptiness in every universe.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicTopology

/-- The existing universe-polymorphic integral coefficient object is nonzero. -/
theorem singularIntegralCoefficients_not_isZero :
    ¬ IsZero (singularIntegralCoefficients.{u}) := by
  intro h
  have hid : (𝟙 (singularIntegralCoefficients.{u}) :
      singularIntegralCoefficients.{u} ⟶ singularIntegralCoefficients.{u}) = 0 :=
    h.eq_of_src _ _
  have h10 := congrArg
    (fun g : singularIntegralCoefficients.{u} ⟶ singularIntegralCoefficients.{u} =>
      (g.hom (ULift.up (1 : ℤ))).down) hid
  exact one_ne_zero (show (1 : ℤ) = 0 from h10)

end AlgebraicTopology

private theorem subsingleton_of_mono_coproduct_fold
    {J : Type u} {C : Type v} [Category.{w} C]
    [Preadditive C] [HasCoproducts.{u} C]
    (R : C) (hR : ¬ IsZero R)
    [Mono (Sigma.desc (fun _ : J => 𝟙 R))] : Subsingleton J := by
  classical
  refine ⟨fun a b => ?_⟩
  by_contra hab
  let S : C := ∐ (fun _ : J => R)
  let π : S ⟶ R := Sigma.desc (fun _ : J => 𝟙 R)
  let χ : S ⟶ R := Sigma.desc (fun j : J => if j = a then 𝟙 R else 0)
  have hi : (Sigma.ι (fun _ : J => R) a : R ⟶ S) = Sigma.ι (fun _ : J => R) b :=
    (cancel_mono π).1 (by simp [π])
  have hχ := congrArg (fun k : R ⟶ S => k ≫ χ) hi
  have hid : (𝟙 R : R ⟶ R) = 0 := by
    simpa [χ, hab, Ne.symm hab] using hχ
  exact hR ((IsZero.iff_id_eq_zero R).2 hid)

namespace TopCat

/-- Zero original reduced integral H₀ makes the original pointed space path connected. -/
theorem pathConnectedSpace_of_isZero_reducedIntegralH0
    (X : TopCat.{u}) (x₀ : X)
    (h : IsZero (AlgebraicTopology.reducedSingularHomology AddCommGrpCat.{u}
      AlgebraicTopology.singularIntegralCoefficients.{u} 0 X)) :
    PathConnectedSpace X := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients.{u}
  let H : AddCommGrpCat.{u} :=
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} 0).obj R).obj X
  let S : AddCommGrpCat.{u} := ∐ (fun _ : ZerothHomotopy X => R)
  let ε : H ⟶ R := X.singularHomology₀ε R
  let e : H ≅ S := X.singularHomology₀Iso R
  let π : S ⟶ R := Sigma.desc (fun _ : ZerothHomotopy X => 𝟙 R)
  have hK : IsZero (kernel ε) :=
    h.of_iso (AlgebraicTopology.reducedSingularHomologyZeroCanonicalKernelIso
      AddCommGrpCat.{u} R X).symm
  have hι : kernel.ι ε = 0 := hK.eq_of_src _ _
  have : Mono ε := Abelian.mono_of_kernel_ι_eq_zero ε hι
  have he : (e.hom : H ⟶ S) ≫ π = ε :=
    X.singularHomology₀Iso_sigma_desc_id R
  have hinv : (e.inv : S ⟶ H) ≫ ε = π := by
    calc
      (e.inv : S ⟶ H) ≫ ε = e.inv ≫ (e.hom ≫ π) :=
        congrArg (fun q : H ⟶ R => e.inv ≫ q) he.symm
      _ = (e.inv ≫ e.hom) ≫ π := (Category.assoc _ _ _).symm
      _ = π := by rw [e.inv_hom_id, Category.id_comp]
  have : Mono ((e.inv : S ⟶ H) ≫ ε) := inferInstance
  have : Mono π := by
    rw [← hinv]
    infer_instance
  have hJ : Subsingleton (ZerothHomotopy X) :=
    subsingleton_of_mono_coproduct_fold R
      AlgebraicTopology.singularIntegralCoefficients_not_isZero
  exact pathConnectedSpace_iff_zerothHomotopy.2 ⟨⟨ZerothHomotopy.mk x₀⟩, hJ⟩

/-- For the original pointed space in every universe, reduced integral H₀
vanishes exactly when its original path-component set has one component. -/
theorem isZero_reducedIntegralH0_iff_pathConnectedSpace
    (X : TopCat.{u}) (x₀ : X) :
    IsZero (AlgebraicTopology.reducedSingularHomology AddCommGrpCat.{u}
      AlgebraicTopology.singularIntegralCoefficients.{u} 0 X) ↔
        PathConnectedSpace X := by
  constructor
  · exact pathConnectedSpace_of_isZero_reducedIntegralH0 X x₀
  · intro hX
    let _ : PathConnectedSpace X := hX
    exact AlgebraicTopology.isZero_reducedSingularHomologyZero_of_pathConnectedSpace
      AddCommGrpCat.{u} AlgebraicTopology.singularIntegralCoefficients.{u} X

end TopCat

end
