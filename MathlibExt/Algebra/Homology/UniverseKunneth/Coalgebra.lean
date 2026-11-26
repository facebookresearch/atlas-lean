/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.UniverseKunneth.Field
public import MathlibExt.Algebra.Homology.HomologyCoalgebra.Diagonal
public import MathlibExt.CategoryTheory.GradedObject.Kernels
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Field homology coalgebras and primitive comparison maps

Let k be a field in universe u and W=max(u,v) an independently chosen common coefficient
universe. The cycle Künneth tensorator μ:H(C)⊗H(D)≅H(C⊗D) and the unit comparison e:𝟙≅H(𝟙) make
graded homology monoidal on chain complexes of shape down ℕ. A chain coalgebra C therefore gives
a graded homology coalgebra with Δ_H=H(Δ_C)≫μ^{-1} and ε_H=H(ε_C)≫e^{-1}. A coalgebra
coaugmentation η induces e≫H(η), and chain Koszul cocommutativity implies graded Koszul
cocommutativity.

For any unit-to-C chain map η, define the reduced coproduct
d_η=Δ_C−((id⊗η)ρ_C^{-1}+(η⊗id)λ_C^{-1}). Its kernel is the corresponding primitive subcomplex.
The Künneth comparison carries H(d_η) to the same reduced-coproduct equation on H(C), using the
induced unit map. This yields a canonical kernel-lift map H(ker d_η)→ker d_{Hη}, characterized
by its composite with the primitive-kernel inclusion.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace HomologicalComplex.UniverseKunneth

variable {k : Type u} [Field k]

private theorem monoidal_ε :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ (homologyFunctor (R := k))
      (monoidalOfField (k := k)).toLaxMonoidal = unitMap.{u,v} (R := k) := rfl

private theorem monoidal_μ (A B : ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ (homologyFunctor (R := k))
      (monoidalOfField (k := k)).toLaxMonoidal A B = tensorator A B := rfl


/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). On k-linear chain complexes of shape down ℕ, graded homology has the monoidal
structure with unit map e:𝟙≅H(𝟙) and tensorator μ_{C,D}:H(C)⊗H(D)≅H(C⊗D) given by the canonical
cycle Künneth map. The field Künneth theorem makes each tensorator invertible. -/
local instance canonicalHomologyMonoidal : (homologyFunctor (R := k)).Monoidal := monoidalOfField
local instance canonicalTensoratorIsIso (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
  : IsIso (tensorator K L) :=
  isIso_tensorator_of_field K L

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). The monoidal graded-homology functor H on chain complexes of shape down ℕ induces
this functor from chain coalgebras to ℕ-graded coalgebras. It sends C to H(C), with
comultiplication H(Δ_C)≫μ_{C,C}^{-1} and counit H(ε_C)≫e^{-1}, and sends a coalgebra morphism f
to H(f). -/
def comonFunctor : Comon (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⥤ Comon (GradedObject
  ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  exact (homologyFunctor (R := k)).mapComon

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain complex C of shape down ℕ equipped with a coalgebra structure, this is
the transported coalgebra structure on H(C). Its comultiplication and counit are
H(Δ_C)≫μ_{C,C}^{-1} and H(ε_C)≫e^{-1}, where μ is the cycle Künneth tensorator and e:𝟙≅H(𝟙) is
the unit comparison. Coassociativity and both counit laws follow from monoidal transport. -/
def comonObj (C : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) [ComonObj C] : ComonObj
  ((homologyFunctor (R := k)).obj C) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  exact Functor.obj.instComonObj C (homologyFunctor (R := k))

variable (C : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) [ComonObj C]

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain coalgebra C of shape down ℕ, let Δ_H:H(C)→H(C)⊗H(C) be its transported
comultiplication and μ_{C,C} the canonical cycle Künneth tensorator. Then
Δ_H≫μ_{C,C}=H(Δ_C):H(C)→H(C⊗C). This determines the homology coproduct through the Künneth
comparison. -/
@[reassoc]
theorem comul_tensorator :
    letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
    Δ[(homologyFunctor (R := k)).obj C] ≫ tensorator C C = HomologyCoalgebra.canonicalToTensorHomology C := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  change ((homologyFunctor (R := k)).map Δ[C] ≫ Functor.OplaxMonoidal.δ (homologyFunctor (R := k)) C C) ≫
    Functor.LaxMonoidal.μ (homologyFunctor (R := k)) C C = (homologyFunctor (R := k)).map Δ[C]
  rw [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). Let C be a chain coalgebra of shape down ℕ, ε_H:H(C)→𝟙 its transported homology
counit and e:𝟙→H(𝟙) the canonical unit map. Then ε_H≫e=H(ε_C). Thus the counit agrees with the
chain counit's homology map after the tensor-unit identification. -/
@[reassoc]
theorem counit_unitMap :
    letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
    ε[(homologyFunctor (R := k)).obj C] ≫ unitMap = (homologyFunctor (R := k)).map ε[C] := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  change ((homologyFunctor (R := k)).map ε[C] ≫ Functor.OplaxMonoidal.η (homologyFunctor (R := k))) ≫
    Functor.LaxMonoidal.ε (homologyFunctor (R := k)) = (homologyFunctor (R := k)).map ε[C]
  rw [Category.assoc, Functor.Monoidal.η_ε, Category.comp_id]

attribute [local instance] ComonObj.instTensorUnit

private theorem unitMap_comul :
    unitMap (R := k) ≫ (homologyFunctor (R := k)).map Δ[𝟙_ (ChainComplex
      (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)] =
      Δ[𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))] ≫ (unitMap ⊗ₘ unitMap) ≫ tensorator
        (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) (𝟙_ (ChainComplex
          (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  change unitMap ≫ (homologyFunctor (R := k)).map (λ_ (𝟙_ (ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))).inv =
    (λ_ (𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)))).inv ≫ (unitMap ⊗ₘ unitMap) ≫
      tensorator (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) (𝟙_ (ChainComplex
        (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
  have hU := Functor.LaxMonoidal.left_unitality_inv (homologyFunctor (R := k))
    (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
  simp only [monoidal_ε, monoidal_μ] at hU
  rw [← hU]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, tensorHom_def, monoidal_ε, monoidal_μ]
  exact congrArg (fun x =>
    (λ_ (𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)))).inv ≫ x ≫
      tensorator (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
        (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)))
    (whisker_exchange (unitMap.{u,v} (R := k)) (unitMap.{u,v} (R := k)))

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain coalgebra C of shape down ℕ and a chain map η:𝟙→C, this map 𝟙→H(C) is
e≫H(η), where e:𝟙≅H(𝟙) is the homology unit comparison. If η is a coalgebra morphism, this is
the induced homology coaugmentation. -/
def coaug (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) : 𝟙_ (GradedObject ℕ
  (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)) ⟶ (homologyFunctor (R := k)).obj C := unitMap ≫
    (homologyFunctor (R := k)).map η

theorem coaugIsComonHom (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C)
  [IsComonHom η] :
    letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
    IsComonHom (coaug C η) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  exact
    { hom_counit := by
        change (unitMap ≫ (homologyFunctor (R := k)).map η) ≫ ((homologyFunctor (R := k)).map ε[C] ≫
          Functor.OplaxMonoidal.η (homologyFunctor (R := k))) = 𝟙 _
        simp only [Category.assoc, ← Functor.map_comp_assoc, IsComonHom.hom_counit,
          ComonObj.instTensorUnit_counit, Functor.map_id, Category.id_comp]
        rw [(homologyFunctor (R := k)).map_id, Category.id_comp]
        simpa only [monoidal_ε] using Functor.Monoidal.ε_η (homologyFunctor (R := k))
      hom_comul := by
        apply (cancel_mono (tensorator C C)).1
        rw [Category.assoc, comul_tensorator]
        simp only [coaug, HomologyCoalgebra.canonicalToTensorHomology,
          Category.assoc, ← Functor.map_comp]
        rw [IsComonHom.hom_comul, Functor.map_comp, ← Category.assoc, unitMap_comul]
        have hT := congrArg (fun x =>
          Δ[𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))] ≫
            (unitMap ⊗ₘ unitMap) ≫ x) (tensorator_naturality η η).symm
        simpa only [Category.assoc, ← MonoidalCategory.tensorHom_comp_tensorHom] using hT
        }

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain coalgebra C of shape down ℕ and a coalgebra morphism η:𝟙→C, this is the
graded homology coalgebra with coaugmentation e≫H(η). It is an object under the trivial graded
tensor-unit coalgebra, with underlying coalgebra H(C) and its transported comultiplication and
counit. -/
def coaugmented (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) [IsComonHom η] :
  Under (Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))) := by
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  letI : IsComonHom (coaug C η) := coaugIsComonHom C η
  exact Under.mk
    (show Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)) ⟶
      ({ X := (homologyFunctor (R := k)).obj C, comon := comonObj C } :
        Comon (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))) from
      Comon.Hom.mk (coaug C η) (isComonHom_hom := coaugIsComonHom C η))

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). Let C be a chain coalgebra of shape down ℕ and assume Δ_C≫b_{C,C}.hom=Δ_C for the
chain Koszul braiding b. Its homology coproduct satisfies Δ_H≫σ_{H(C),H(C)}.hom=Δ_H, where σ is
the graded Koszul interchange with bidegree sign (-1)^{pq}. The equality follows by transporting
the given chain equation through the canonical tensorator. -/
theorem comul_cocommutative (h : Δ[C] ≫ (koszulTensorBraidingIso C C).hom = Δ[C]) :
    letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
    Δ[(homologyFunctor (R := k)).obj C] ≫ (koszulSwap ((homologyFunctor (R := k)).obj C) ((homologyFunctor (R :=
      k)).obj C)).hom = Δ[(homologyFunctor (R := k)).obj C] := by
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  letI : IsIso (tensorator C C) := isIso_tensorator_of_field C C
  apply (cancel_mono (tensorator C C)).1
  rw [Category.assoc, ← tensorator_braiding, ← Category.assoc, comul_tensorator]
  change HomologyCoalgebra.canonicalToTensorHomology C ≫ _ =
    HomologyCoalgebra.canonicalToTensorHomology C
  simp only [HomologyCoalgebra.canonicalToTensorHomology, ← Functor.map_comp, h]

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain coalgebra C of shape down ℕ and any chain map η:𝟙→C, the primitive
equation is the map d_η:C→C⊗C given by Δ_C−(ρ_C^{-1}≫(id_C⊗η)+λ_C^{-1}≫(η⊗id_C)). Its kernel
consists of the elements whose coproduct is the sum of these two η-unit terms. -/
def primitiveEquation (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) : C ⟶ C ⊗ C :=
  Δ[C] - ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C))

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain coalgebra C of shape down ℕ and a chain map η:𝟙→C, this chain complex is
ker(d_η), with d_η=Δ_C−(ρ_C^{-1}≫(id⊗η)+λ_C^{-1}≫(η⊗id)). Its canonical inclusion into C is
killed by the reduced coproduct, so it defines the primitive subcomplex relative to η. -/
def primitiveComplex (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) :
  (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) := kernel (primitiveEquation C η)

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain coalgebra C of shape down ℕ and a chain map η:𝟙→C, let a=e≫H(η):𝟙→H(C)
and Δ_H be the transported homology coproduct. This graded map d_a:H(C)→H(C)⊗H(C) is
Δ_H−(ρ_{H(C)}^{-1}≫(id⊗a)+λ_{H(C)}^{-1}≫(a⊗id)). It is the primitive equation relative to the
induced homology unit map. -/
def homologyPrimitiveEquation (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) :
  (homologyFunctor (R := k)).obj C ⟶ (homologyFunctor (R := k)).obj C ⊗ (homologyFunctor (R := k)).obj C := by
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  exact Δ[(homologyFunctor (R := k)).obj C] - ((ρ_ ((homologyFunctor (R := k)).obj C)).inv ≫ (𝟙 ((homologyFunctor (R
    := k)).obj C) ⊗ₘ coaug C η) +
    (λ_ ((homologyFunctor (R := k)).obj C)).inv ≫ (coaug C η ⊗ₘ 𝟙 ((homologyFunctor (R := k)).obj C)))

omit [ComonObj C] in
private theorem unitTerms_transport (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶
  C) :
    (homologyFunctor (R := k)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C)) ≫
      inv (tensorator C C) =
    (ρ_ ((homologyFunctor (R := k)).obj C)).inv ≫ (𝟙 ((homologyFunctor (R := k)).obj C) ⊗ₘ coaug C η) +
      (λ_ ((homologyFunctor (R := k)).obj C)).inv ≫ (coaug C η ⊗ₘ 𝟙 ((homologyFunctor (R := k)).obj C)) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : IsIso (tensorator C C) := isIso_tensorator_of_field C C
  apply (cancel_mono (tensorator C C)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Preadditive.add_comp]
  have ha : (homologyFunctor (R := k)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C)) =
      (homologyFunctor (R := k)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η)) + (homologyFunctor (R := k)).map ((λ_ C).inv ≫ (η ⊗ₘ 𝟙
        C)) := by
    funext n
    exact homologyMap_add _ _ n
  rw [ha, Functor.map_comp, Functor.map_comp,
    ← Functor.LaxMonoidal.right_unitality_inv, ← Functor.LaxMonoidal.left_unitality_inv]
  simp only [monoidal_ε, monoidal_μ, Category.assoc]
  have hRight := tensorator_naturality (𝟙 C) η
  have hLeft := tensorator_naturality η (𝟙 C)
  rw [(homologyFunctor (R := k)).map_id C] at hRight hLeft
  rw [← hRight, ← hLeft]
  simp only [coaug, Functor.map_id, ← tensorHom_comp_tensorHom_assoc,
    Category.id_comp, tensorHom_def, tensorHom_def', Category.assoc,
    id_whiskerRight, whiskerLeft_id, whiskerLeft_comp, comp_whiskerRight]

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain coalgebra C of shape down ℕ and a chain map η:𝟙→C, write d_η for the
reduced chain coproduct and d_a for the homology primitive equation with a=e≫H(η). Then
H(d_η)≫μ_{C,C}^{-1}=d_a, where μ_{C,C}:H(C)⊗H(C)≅H(C⊗C) is the canonical cycle Künneth
tensorator. -/
theorem primitiveEquation_transport (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶
  C) :
    (homologyFunctor (R := k)).map (primitiveEquation C η) ≫ inv (tensorator C C) = homologyPrimitiveEquation C η := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : IsIso (tensorator C C) := isIso_tensorator_of_field C C
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  have hs : (homologyFunctor (R := k)).map (primitiveEquation C η) = (homologyFunctor (R := k)).map Δ[C] -
      (homologyFunctor (R := k)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C)) := by
    funext n
    exact homologyMap_sub _ _ n
  have hd : (homologyFunctor (R := k)).map Δ[C] ≫ inv (tensorator C C) = Δ[(homologyFunctor (R := k)).obj C] := by
    have h := comul_tensorator C
    apply (cancel_mono (tensorator C C)).1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact h.symm
  rw [hs, Preadditive.sub_comp, hd, unitTerms_transport]
  rfl

/-- Let k be a field in universe u, v an independent lift height, and all coefficient modules lie in
W=max(u,v). For a chain coalgebra C of shape down ℕ and a chain map η:𝟙→C, let i:ker(d_η)→C and
j:ker(d_a)→H(C) be the chain and homology primitive-kernel inclusions. The canonical comparison
κ:H(ker d_η)→ker d_a is the kernel lift of H(i), characterized by κ≫j=H(i). The
primitive-equation transport proves that H(i) is killed by d_a. -/
def primitiveComparison (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) :
    (homologyFunctor (R := k)).obj (primitiveComplex C η) ⟶ kernel (homologyPrimitiveEquation C η) := by
  letI : IsIso (tensorator C C) := isIso_tensorator_of_field C C
  let i : kernel (primitiveEquation C η) ⟶ C := kernel.ι (primitiveEquation C η)
  have hK : i ≫ primitiveEquation C η = 0 := kernel.condition _
  have hMap := congrArg (homologyFunctor (R := k)).map hK
  rw [Functor.map_comp] at hMap
  have hz : homologyFunctor.map (0 : kernel (primitiveEquation C η) ⟶ C ⊗ C) = 0 := by
    funext n
    exact homologyMap_zero _ _ n
  have hLift : homologyFunctor.map i ≫ homologyPrimitiveEquation C η = 0 := by
    rw [← primitiveEquation_transport]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x => x ≫ inv (tensorator C C)) hMap).trans
        ((congrArg (fun x => x ≫ inv (tensorator C C)) hz).trans zero_comp))
  exact kernel.lift (homologyPrimitiveEquation C η) (homologyFunctor.map i) hLift

@[reassoc (attr := simp)]
theorem primitiveComparison_ι (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) :
    primitiveComparison C η ≫ kernel.ι (homologyPrimitiveEquation C η) =
      (homologyFunctor (R := k)).map (kernel.ι (primitiveEquation C η)) := by
  unfold primitiveComparison
  exact kernel.lift_ι _ _ _

end HomologicalComplex.UniverseKunneth
