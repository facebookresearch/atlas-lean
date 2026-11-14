/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b:
* StacksFrontier/Algebra/Homology/DerivedCategory/HomToInjectiveSingle.lean;
* StacksFrontier/Algebra/Homology/DerivedCategory/ProjectiveCorepresents.lean;
* StacksFrontier/Algebra/Homology/DerivedCategory/InjectiveRepresents.lean.
These sources are licensed under Apache 2.0 and carry no individual
author or copyright notice. Modification notice: isolate the existing
completed proofs and scalar comparison in the MathlibExt namespace and
use the pinned Mathlib API.
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Morphisms into an injective object placed in one degree

Let `C` be an abelian category, `E` an injective object and `i` an integer. For every object `X`
of `D(C)`, taking degree-`i` cohomology is a bijection from morphisms `X ⟶ E[-i]` (the object
`E` placed in degree `i`) to morphisms `Hⁱ(X) ⟶ E`. The bijection is natural in `X`, being
induced by the functor `Hⁱ`.

## Main results

* `DerivedCategory.bijective_homologyMap_comp_of_injective` — the bijection.

## Implementation notes

The complex `E[-i]` is K-injective, so morphisms into it from a complex `K` are homotopy classes
of chain maps; a chain map `K ⟶ E[-i]` is a map `Kⁱ ⟶ E` killing the boundaries, it is
null-homotopic exactly when it kills the cycles, and every map `Hⁱ(K) ⟶ E` extends to `Kⁱ` by
injectivity of `E`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace MathlibExt.HomologicalAlgebra.InjectiveSingleHom

namespace CochainComplex

/-- Every term of an injective object placed in degree `i` is injective. -/
private instance injective_singleFunctor_obj_X (E : C) [Injective E] (i j : ℤ) :
    Injective (((CochainComplex.singleFunctor C i).obj E).X j) :=
  inferInstanceAs (Injective (((single C (ComplexShape.up ℤ) i).obj E).X j))

/-- Cohomology of a chain map into `E` placed in degree `i`, seen on cycles. -/
private theorem homologyπ_homologyMap_single_hom (K : CochainComplex C ℤ) (E : C) (i : ℤ)
    (g : K ⟶ (CochainComplex.singleFunctor C i).obj E) :
    K.homologyπ i ≫ homologyMap g i ≫ (singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom =
      K.iCycles i ≫ g.f i ≫ (singleObjXSelf (ComplexShape.up ℤ) i E).hom := by
  simp only [CochainComplex.singleFunctor] at g ⊢
  rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom, cyclesMap_i_assoc]

/-- Every map from the degree-`i` cohomology of a complex to an injective object is the
cohomology of a chain map into that object placed in degree `i`. -/
theorem exists_homologyMap_toSingle_of_injective (K : CochainComplex C ℤ) (E : C) [Injective E]
    (i : ℤ) (f : K.homology i ⟶ E) :
    ∃ g : K ⟶ (CochainComplex.singleFunctor C i).obj E,
      homologyMap g i ≫ (singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom = f := by
  simp only [CochainComplex.singleFunctor]
  let t := Injective.factorThru f (K.homologyι i)
  let g : K ⟶ (CochainComplex.singleFunctor C i).obj E :=
    mkHomToSingle (K.pOpcycles i ≫ t) (by intros; simp)
  refine ⟨g, ?_⟩
  apply (cancel_epi (K.homologyπ i)).mp
  rw [homologyπ_homologyMap_single_hom]
  dsimp [g]
  rw [mkHomToSingle_f]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← homology_π_ι, Category.assoc]
  exact congrArg (fun q => K.homologyπ i ≫ q) (Injective.comp_factorThru f (K.homologyι i))

/-- A chain map into an injective object placed in degree `i` that vanishes on degree-`i`
cohomology is null-homotopic. -/
theorem nonempty_homotopy_zero_of_homologyMap_eq_zero (K : CochainComplex C ℤ) (E : C)
    [Injective E] (i : ℤ) (f : K ⟶ (CochainComplex.singleFunctor C i).obj E)
    (hf : homologyMap f i = 0) : Nonempty (Homotopy f 0) := by
  classical
  dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] at f hf ⊢
  let J := (CochainComplex.singleFunctor C i).obj E
  have hz : K.iCycles i ≫ f.f i = 0 := by
    have h := homologyπ_homologyMap_single_hom K E i f
    rw [hf, zero_comp, comp_zero] at h
    exact (cancel_mono (singleObjXSelf (ComplexShape.up ℤ) i E).hom).mp (by simpa using h.symm)
  let S := ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1))
  have hS : S.Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i (i + 1) (by simp))
  let t : K.X (i + 1) ⟶ J.X i := hS.descToInjective (f.f i) hz
  let h : ∀ a b, K.X a ⟶ J.X b := fun a b =>
    if ha : a = i + 1 then if hb : b = i then eqToHom (congrArg K.X ha) ≫ t ≫
      eqToHom (congrArg J.X hb.symm) else 0 else 0
  have heq : f = Homotopy.nullHomotopicMap h := by
    apply to_single_hom_ext
    change f.f i = _
    simp only [Homotopy.nullHomotopicMap, dNext, prevD, h]
    simpa [S] using (hS.comp_descToInjective (f.f i) hz).symm
  rw [heq]
  refine ⟨Homotopy.nullHomotopy h fun a b hab ↦ ?_⟩
  dsimp [h]
  split_ifs with ha hb
  · subst a b
    exact (hab (by simp)).elim
  all_goals rfl

end CochainComplex

namespace DerivedCategory

open _root_.DerivedCategory

variable [HasDerivedCategory.{w} C]

/-- Morphisms in `D(C)` into a K-injective complex all come from chain maps. -/
theorem Q_map_surjective_of_isKInjective (K L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Surjective (Q.map : (K ⟶ L) → (Q.obj K ⟶ Q.obj L)) := by
  intro ψ
  obtain ⟨g', hg'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective _ L).surjective
    ((quotientCompQhIso C).hom.app K ≫ ψ ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective g'
  refine ⟨g, ?_⟩
  have h := quotientCompQhIso_hom_naturality g
  rw [hg'] at h
  simpa using h.symm

/-- The canonical identification `Hⁱ(E[-i]) ≅ E`, for the cochain complex `E[-i]`, with its
source spelled through the homology functor. -/
abbrev singleHomologyIso (E : C) (i : ℤ) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj
      ((CochainComplex.singleFunctor C i).obj E) ≅ E :=
  singleObjHomologySelfIso (ComplexShape.up ℤ) i E

/-- The degree-`i` cohomology functor of `D(C)` identifies morphisms from `Q(K)` into an
injective object placed in degree `i` with morphisms out of `Hⁱ(K)`. -/
private theorem bijective_homologyMap_Q_single (K : CochainComplex C ℤ) (E : C) [Injective E]
    (i : ℤ) :
    Function.Bijective (fun ψ : Q.obj K ⟶ Q.obj ((CochainComplex.singleFunctor C i).obj E) ↦
      (homologyFunctorFactors C i).inv.app K ≫ (homologyFunctor C i).map ψ ≫
        (homologyFunctorFactors C i).hom.app _ ≫ (singleHomologyIso E i).hom) := by
  let J := (CochainComplex.singleFunctor C i).obj E
  have : J.IsStrictlyGE i := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J i
  have hQ : ∀ g : K ⟶ J, (homologyFunctorFactors C i).inv.app K ≫
      (homologyFunctor C i).map (Q.map g) ≫ (homologyFunctorFactors C i).hom.app J ≫
        (singleHomologyIso E i).hom =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).map g ≫
        (singleHomologyIso E i).hom := by
    intro g
    rw [reassoc_of% ((homologyFunctorFactors C i).hom.naturality g), Iso.inv_hom_id_app_assoc]
  refine ⟨fun ψ₁ ψ₂ hψ ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨g₁, rfl⟩ := Q_map_surjective_of_isKInjective K J ψ₁
    obtain ⟨g₂, rfl⟩ := Q_map_surjective_of_isKInjective K J ψ₂
    have hψ' := (hQ g₁).symm.trans (hψ.trans (hQ g₂))
    rw [cancel_mono] at hψ'
    have h0 : homologyMap (g₁ - g₂) i = 0 := by
      change (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).map (g₁ - g₂) = 0
      rw [Functor.map_sub, hψ', sub_self]
    obtain ⟨H⟩ := CochainComplex.nonempty_homotopy_zero_of_homologyMap_eq_zero K E i _ h0
    exact Q_map_eq_of_homotopy C (Homotopy.equivSubZero.symm H)
  · obtain ⟨g, hg⟩ := CochainComplex.exists_homologyMap_toSingle_of_injective K E i f
    exact ⟨Q.map g, (hQ g).trans hg⟩

/-- **Morphisms into an injective object placed in one degree are detected on cohomology.**
For an injective object `E` of an abelian category `C` and an object `X` of `D(C)`, the map
`(X ⟶ E[-i]) → (Hⁱ(X) ⟶ E)` sending `φ` to `Hⁱ(φ)` followed by the canonical identification
`Hⁱ(E[-i]) ≅ E` is bijective. It is natural in `X`, being induced by the functor `Hⁱ`. -/
theorem bijective_homologyMap_comp_of_injective (X : DerivedCategory C) (E : C) [Injective E]
    (i : ℤ) :
    Function.Bijective (fun φ : X ⟶ (singleFunctor C i).obj E ↦
      (homologyFunctor C i).map φ ≫ (singleFunctorCompHomologyFunctorIso C i).hom.app E) := by
  let K := Q.objPreimage X
  let e : Q.obj K ≅ X := Q.objObjPreimageIso X
  let J := (CochainComplex.singleFunctor C i).obj E
  let s : (singleFunctor C i).obj E ≅ Q.obj J := (singleFunctorIsoCompQ C i).app E
  let Φ := fun ψ : Q.obj K ⟶ Q.obj J ↦
    (homologyFunctorFactors C i).inv.app K ≫ (homologyFunctor C i).map ψ ≫
      (homologyFunctorFactors C i).hom.app J ≫ (singleHomologyIso E i).hom
  let T := fun φ : X ⟶ (singleFunctor C i).obj E ↦ e.hom ≫ φ ≫ s.hom
  let w : E ≅ E := (singleHomologyIso E i).symm ≪≫ ((homologyFunctorFactors C i).app J).symm ≪≫
    (homologyFunctor C i).mapIso s.symm ≪≫ (singleFunctorCompHomologyFunctorIso C i).app E
  let uI := (homologyFunctor C i).mapIso e.symm ≪≫ (homologyFunctorFactors C i).app K
  let G := fun x : K.homology i ⟶ E ↦ uI.hom ≫ x ≫ w.hom
  have hcomp : (fun φ : X ⟶ (singleFunctor C i).obj E ↦
      (homologyFunctor C i).map φ ≫ (singleFunctorCompHomologyFunctorIso C i).hom.app E) =
      G ∘ Φ ∘ T := by
    funext φ
    change _ = G (Φ (T φ))
    dsimp only [G, Φ, T, w, uI]
    simp
  rw [hcomp]
  exact (uI.symm.homCongr w).bijective.comp
    ((bijective_homologyMap_Q_single K E i).comp (e.symm.homCongr s).bijective)


/-- Cohomology is linear in the actual derived-category morphisms.
This is the existing Axiom ProjectiveCorepresents proof, localized from
the actual cochain homology map. -/
theorem homologyFunctorLinear (R : Type*) [Ring R] [Linear R C] (i : ℤ) :
    Functor.Linear R (_root_.DerivedCategory.homologyFunctor C i) := by
  have : Functor.Linear R (HomologicalComplex.homologyFunctor C (.up ℤ) i) := by
    refine ⟨fun g r ↦ ?_⟩
    change HomologicalComplex.homologyMap (r • g) i =
      r • HomologicalComplex.homologyMap g i
    rw [HomologicalComplex.homologyMap, HomologicalComplex.homologyMap,
      show (HomologicalComplex.shortComplexFunctor C (.up ℤ) i).map (r • g) =
        r • (HomologicalComplex.shortComplexFunctor C (.up ℤ) i).map g from by ext <;> rfl]
    exact ShortComplex.homologyMap_smul _ _
  exact (Localization.functor_linear_iff _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) R
    (_root_.DerivedCategory.Q ⋙ _root_.DerivedCategory.homologyFunctor C i)
    (_root_.DerivedCategory.homologyFunctor C i)).mp
      (Functor.linear_of_iso R (_root_.DerivedCategory.homologyFunctorFactors C i).symm)

/-- Taking cohomology identifies maps to an injective single object,
with the full scalar action retained. -/
def homToInjectiveSingleLinearEquiv (R : Type*) [Ring R] [Linear R C]
    (X : _root_.DerivedCategory C) (E : C) [Injective E] (i : ℤ) :
    (X ⟶ (_root_.DerivedCategory.singleFunctor C i).obj E) ≃ₗ[R]
      ((_root_.DerivedCategory.homologyFunctor C i).obj X ⟶ E) := by
  have := homologyFunctorLinear (C := C) R i
  let f :
      (X ⟶ (_root_.DerivedCategory.singleFunctor C i).obj E) →ₗ[R]
        ((_root_.DerivedCategory.homologyFunctor C i).obj X ⟶ E) :=
    { toFun a := (_root_.DerivedCategory.homologyFunctor C i).map a ≫
        (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app E
      map_add' a b := by simp [Functor.map_add, Preadditive.add_comp]
      map_smul' r a := by simp [Functor.map_smul, Linear.smul_comp] }
  exact LinearEquiv.ofBijective f (bijective_homologyMap_comp_of_injective X E i)


end DerivedCategory

end MathlibExt.HomologicalAlgebra.InjectiveSingleHom

