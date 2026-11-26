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

public import MathlibExt.Algebra.Homology.HomComplex.Map
public import Mathlib.Algebra.Homology.Additive

/-!
# Linear product Hom-complex bifunctors

Let R be a ring and C a preadditive R-linear category with independent scalar, object and
morphism universes. For integer cochain complexes K,L, degree n of the Hom complex is the
product ∏_{i∈ℤ}Hom_C(K_i,L_{i+n}), with R-module carrier in the morphism universe. Its
differential is (δz)_i=z_i≫d_L+(-1)^{n+1}d_K≫z_{i+1}.

A source map f:K′→K and target map g:L→L′ act by z_i↦f_i≫z_i≫g_{i+n}. These maps preserve the
differential, identities and composition, and are additive in each complex variable. They give
an unbounded Hom-complex bifunctor, contravariant in K and covariant in L. Forgetting R-scalars
identifies it with the additive product Hom complex and its corresponding maps. No
bounded-support hypothesis is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CochainComplex.HomComplex

universe uC vC uR

variable (R : Type uR) [Ring R]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
  {K K' K'' L L' L'' : CochainComplex C ℤ}

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For cochain complexes K,L of shape up ℤ, this complex has
degree-n module ∏_{i∈ℤ}Hom_C(K_i,L_{i+n}) in vC. Its differential is
(δz)_i=z_i≫d_L(i+n,i+n+1)+(-1)^{n+1}d_K(i,i+1)≫z_{i+1}. The product includes every integer
source degree. -/
@[implicit_reducible]
def linearComplex (K L : CochainComplex C ℤ) : CochainComplex (ModuleCat.{vC} R) ℤ :=
  CochainComplex.linearHomComplex R K L

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For integer cochain maps f:K′→K and g:L→L′, this R-linear
cochain map Hom(K,L)→Hom(K′,L′) sends a degree-n family z to the family f_i≫z_i≫g_{i+n}. The
component formula commutes with the product Hom differential. -/
def linearComplexMap (f : K' ⟶ K) (g : L ⟶ L') :
    linearComplex R K L ⟶ linearComplex R K' L' where
  f n := ModuleCat.ofHom (mapLinearOver R f g n)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change δ i j (mapLinearOver R f g i z) = mapLinearOver R f g j (δ i j z)
    exact (mapLinearOver_δ R f g i j z).symm

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For integer cochain complexes K,L, the map on Hom(K,L)
induced by id_K and id_L is id_{Hom(K,L)}. In each degree n and component i, the formula
id_{K_i}≫z_i≫id_{L_{i+n}} equals z_i. -/
@[simp]
theorem linearComplexMap_id (K L : CochainComplex C ℤ) :
    linearComplexMap R (𝟙 K) (𝟙 L) = 𝟙 (linearComplex R K L) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change mapLinearOver R (𝟙 K) (𝟙 L) n z = z
  exact congrArg (fun h : Cochain K L n →ₗ[R] Cochain K L n => h z)
    (mapLinearOver_id R K L n)

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For integer cochain maps f:K′→K, f′:K″→K′, g:L→L′ and
g′:L′→L″, the induced maps satisfy H(f,g)≫H(f′,g′)=H(f′≫f,g≫g′). Both sides map Hom(K,L) to
Hom(K″,L″) through degreewise precomposition and postcomposition. -/
theorem linearComplexMap_comp (f : K' ⟶ K) (f' : K'' ⟶ K')
    (g : L ⟶ L') (g' : L' ⟶ L'') :
    linearComplexMap R f g ≫ linearComplexMap R f' g' =
      linearComplexMap R (f' ≫ f) (g ≫ g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change mapLinearOver R f' g' n (mapLinearOver R f g n z) =
    mapLinearOver R (f' ≫ f) (g ≫ g') n z
  exact congrArg (fun h : Cochain K L n →ₗ[R] Cochain K'' L'' n => h z)
    (mapLinearOver_comp R f f' g g' n)

variable (C)

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. The assignment (K,L)↦Hom(K,L), with degree-n product ∏_i
Hom_C(K_i,L_{i+n}) and signed Hom differential, defines a functor from the opposite category of
integer cochain complexes into functors from integer cochain complexes to R-module-valued
cochain complexes. A source map acts by precomposition and a target map by postcomposition. -/
@[implicit_reducible]
def linearFunctor : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤
    CochainComplex (ModuleCat.{vC} R) ℤ where
  obj K :=
    { obj := fun L => linearComplex R K.unop L
      map := fun g => linearComplexMap R (𝟙 K.unop) g
      map_id L := linearComplexMap_id R K.unop L
      map_comp g g' := by
        simpa only [Category.id_comp] using
          (linearComplexMap_comp R (𝟙 K.unop) (𝟙 K.unop) g g').symm }
  map f :=
    { app := fun L => linearComplexMap R f.unop (𝟙 L)
      naturality _ _ g := by
        rw [linearComplexMap_comp, linearComplexMap_comp]
        simp only [Category.id_comp, Category.comp_id] }
  map_id K := by
    apply NatTrans.ext
    funext L
    exact linearComplexMap_id R K.unop L
  map_comp f f' := by
    apply NatTrans.ext
    funext L
    simpa only [NatTrans.comp_app, CategoryTheory.unop_comp, Category.id_comp] using
      (linearComplexMap_comp R f.unop f'.unop (𝟙 L) (𝟙 L)).symm

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For a fixed integer cochain complex K, the functor
L↦Hom(K,L) is additive. Parallel target maps g,g′ induce H(id_K,g+g′)=H(id_K,g)+H(id_K,g′), by
additivity of postcomposition in every product component. -/
instance linearFunctor_obj_additive (K : (CochainComplex C ℤ)ᵒᵖ) :
    ((linearFunctor R C).obj K).Additive where
  map_add {X Y f g} := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    change (mapLinearOver R (𝟙 K.unop) (f + g) n z).v p q hpq =
      (mapLinearOver R (𝟙 K.unop) f n z + mapLinearOver R (𝟙 K.unop) g n z).v p q hpq
    rw [Cochain.add_v, mapLinearOver_v, mapLinearOver_v, mapLinearOver_v]
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex.id_f,
      Category.id_comp, Preadditive.comp_add]

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. The contravariant source functor K↦Hom(K,-) is additive on
the opposite category of integer cochain complexes. Parallel source maps f,f′ induce the sum of
their precomposition natural transformations, degreewise on ∏_i Hom_C(K_i,L_{i+n}). -/
instance linearFunctor_additive : (linearFunctor R C).Additive where
  map_add {X Y f g} := by
    apply NatTrans.ext
    funext L
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    change (mapLinearOver R (f + g).unop (𝟙 L) n z).v p q hpq =
      (mapLinearOver R f.unop (𝟙 L) n z + mapLinearOver R g.unop (𝟙 L) n z).v p q hpq
    rw [Cochain.add_v, mapLinearOver_v, mapLinearOver_v, mapLinearOver_v]
    change (f.unop.f p + g.unop.f p) ≫ z.v p q hpq ≫ 𝟙 _ =
      f.unop.f p ≫ z.v p q hpq ≫ 𝟙 _ + g.unop.f p ≫ z.v p q hpq ≫ 𝟙 _
    simp only [Category.comp_id, Preadditive.add_comp]

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For integer cochain complexes K,L, forgetting the R-module
action on each degree of the linear Hom complex gives a canonical isomorphism with the
additive-group Hom complex. It is the identity on the product cochain families and retains
δz=z≫d_L+(-1)^{n+1}d_K≫z in degree n. -/
def linearComplexForgetIso (K L : CochainComplex C ℤ) :
    ((forget₂ (ModuleCat.{vC} R) AddCommGrpCat.{vC}).mapHomologicalComplex (.up ℤ)).obj
        (linearComplex R K L) ≅ HomComplex K L :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    rfl)

/-- Let R be a ring in universe uR and C a preadditive R-linear category with independent object
universe uC and morphism universe vC. For f:K′→K and g:L→L′, let e_{K,L} be the
scalar-forgetting comparison and U the forgetful functor on cochain complexes. Then
U(H_R(f,g))≫e_{K′,L′}.hom=e_{K,L}.hom≫H_add(f,g). All maps act by the same precomposition and
postcomposition on the product families. -/
@[reassoc]
theorem linearComplexForgetIso_naturality {K K' L L' : CochainComplex C ℤ}
    (f : K' ⟶ K) (g : L ⟶ L') :
    ((forget₂ (ModuleCat.{vC} R) AddCommGrpCat.{vC}).mapHomologicalComplex (.up ℤ)).map
        (linearComplexMap R f g) ≫ (linearComplexForgetIso R C K' L').hom =
      (linearComplexForgetIso R C K L).hom ≫ HomComplex.map f g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  rfl

end CochainComplex.HomComplex

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R]

/-- Let R be a commutative ring in universe u and module carriers lie in an independent universe v.
For R-module-valued cochain complexes K,L of shape up ℤ, this bifunctor assigns the R-linear Hom
complex with degree-n product ∏_i Hom_R(K_i,L_{i+n}) and differential z≫d_L+(-1)^{n+1}d_K≫z. It
is contravariant in K and covariant in L. -/
abbrev homComplexFunctor : (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.HomComplex.linearFunctor R (ModuleCat.{v} R)

end ModuleCat
