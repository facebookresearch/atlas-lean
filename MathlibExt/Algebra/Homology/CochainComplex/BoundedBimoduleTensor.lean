/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BimoduleTensor
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedFunctor

/-!
# Bounded finite-module complexes under bimodule tensoring

Let R,S be rings in universe u and E a commuting left-S/right-R bimodule in that universe,
finite as a left S-module. Tensoring by E gives a functor from bounded cochains of finitely
generated R-modules to bounded cochains of finitely generated S-modules, preserving each
term-support window. Forgetting finite generation commutes with this degreewise tensor.

Homology and quasi-isomorphisms are tested in the ambient module cochain categories. The
Tor₁^R(E,N)=0 criterion gives homology preservation and preservation of these
quasi-isomorphisms. Coefficient maps, coefficient isomorphisms, the regular coefficient, and
composite bimodules give the corresponding bounded natural transformations and isomorphisms.

For an (R,S)-bimodule P and an (S,R)-bimodule Q with bimodule equivalences P⊗_S Q≅R and Q⊗_R
P≅S, the induced Morita equivalence restricts to bounded finite-module cochains. Its forward
functor is Q⊗_R− and its inverse is P⊗_S−, with degreewise unit and counit and preservation of
ambient quasi-isomorphisms.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace CochainComplex.Bounded

variable (R : Type u) [Ring R]

/-- Let R : Type u be a ring. The functor from Bounded(FGModuleCat.{u} R) to
CochainComplex(ModuleCat.{u} R,ℤ) first includes a bounded finite-module complex into all such
cochains, then forgets finite generation degreewise. Its objects retain the module terms and
differentials, and its maps retain their module components. -/
abbrev fgModuleAmbient :
    Bounded (FGModuleCat.{u} R) ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  ι (FGModuleCat.{u} R) ⋙
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)

/-- For a ring R in universe u, define a morphism of bounded FGModuleCat.{u} R cochains to be an
ambient quasi-isomorphism when its image under fgModuleAmbient R is a quasi-isomorphism in the
integer ModuleCat.{u} R cochain category. Homology is computed in all modules, so no abelian
structure on the finite-module category is assumed. -/
abbrev fgModuleQuasiIsomorphisms : MorphismProperty (Bounded (FGModuleCat.{u} R)) :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).inverseImage (fgModuleAmbient R)

/-- Let R be a ring and f : K → L a map in Bounded(FGModuleCat.{u} R). Membership in
fgModuleQuasiIsomorphisms R is equivalent to QuasiIso((fgModuleAmbient R).map f). Thus the
property tests all integer homology maps of the same underlying module cochain morphism. -/
theorem fgModuleQuasiIsomorphisms_iff {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L) :
    fgModuleQuasiIsomorphisms R f ↔ QuasiIso ((fgModuleAmbient R).map f) := Iff.rfl

variable {R}
variable {S : Type u} [Ring S]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E] [Module.Finite S E]

/-- Let R,S be rings in universe u and E a commuting left-S/right-R bimodule, finite over S. The
finite-module tensor functor E⊗_R− restricts degreewise to Bounded(FGModuleCat.{u} R) →
Bounded(FGModuleCat.{u} S). Its output terms are finitely generated over S, and its support
window is inherited from the input. -/
abbrev bimoduleTensor : Bounded (FGModuleCat.{u} R) ⥤ Bounded (FGModuleCat.{u} S) :=
  (FGModuleCat.bimoduleTensor (R := R) (S := S) E).mapCochainComplexBounded

/-- For rings R,S and a commuting left-S/right-R bimodule E finite over S, let K be a bounded
finite R-module cochain complex. The underlying module of its jth tensor term is the ambient
balanced tensor E⊗_R K^j, with the left S-action on E. -/
theorem bimoduleTensor_obj_X_obj (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    (((bimoduleTensor (S := S) E).obj K).obj.X j).obj =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj ((K.obj.X j).obj) := rfl

/-- Let R,S be rings and E a commuting left-S/right-R bimodule finite over S. For a bounded
finite-module cochain complex K and i,j ∈ ℤ, forgetting the output differential of E⊗_R K
gives the ambient balanced tensor map E⊗_R d_K^{i,j}. -/
theorem bimoduleTensor_obj_d_hom (K : Bounded (FGModuleCat.{u} R)) (i j : ℤ) :
    (((bimoduleTensor (S := S) E).obj K).obj.d i j).hom =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map ((K.obj.d i j).hom) := rfl

/-- For a commuting left-S/right-R bimodule E finite over S and a bounded finite R-module cochain
map f : K → L, the underlying jth component of its tensor image is E⊗_R f^j. The component is
computed by the ambient balanced tensor functor. -/
theorem bimoduleTensor_map_f_hom {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L) (j : ℤ) :
    (((bimoduleTensor (S := S) E).map f).hom.f j).hom =
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map ((f.hom.f j).hom) := rfl

/-- Let R,S be rings, E a commuting left-S/right-R bimodule finite over S, and K a bounded cochain
complex of finite R-modules. Every term E⊗_R K^j is finite as an S-module. The input term is
finite over R and the coefficient is finite over the output ring S. -/
theorem bimoduleTensor_obj_finite (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    Module.Finite S (((bimoduleTensor (S := S) E).obj K).obj.X j) := inferInstance

/-- For a commuting left-S/right-R bimodule E finite over S, suppose a bounded finite R-module
complex K has zero terms outside [a,b]. Then the corresponding bounded finite S-module tensor
complex has zero terms at every j<a or j>b. The support interval is unchanged. -/
theorem bimoduleTensor_obj_isZero_outside (K : Bounded (FGModuleCat.{u} R)) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ)
    (hj : j < a ∨ b < j) : IsZero (((bimoduleTensor (S := S) E).obj K).obj.X j) :=
  (FGModuleCat.bimoduleTensor (R := R) (S := S) E).map_isZero (hK j hj)

/-- Let R,S be rings and E a commuting left-S/right-R bimodule finite over S. For K ∈
Bounded(FGModuleCat R), i,j ∈ ℤ, e ∈ E, and x ∈ K^i, the underlying tensor differential sends
[e,x] to [e,d_K^{i,j}(x)]. -/
theorem bimoduleTensor_d_mk (K : Bounded (FGModuleCat.{u} R)) (i j : ℤ)
    (e : E) (x : K.obj.X i) :
    letI : Module ℤ (K.obj.X i) := Module.compHom (K.obj.X i) (algebraMap ℤ R)
    letI : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
    (((bimoduleTensor (S := S) E).obj K).obj.d i j).hom.hom
        (TensorProduct.Balanced.mk ℤ R E (K.obj.X i) e x) =
      TensorProduct.Balanced.mk ℤ R E (K.obj.X j) e ((K.obj.d i j).hom.hom x) := by
  let : Module ℤ (K.obj.X i) := Module.compHom (K.obj.X i) (algebraMap ℤ R)
  let : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
  exact FGModuleCat.bimoduleTensor_map_mk (R := R) (S := S) E (K.obj.d i j) e x

/-- For a commuting left-S/right-R bimodule E finite over S and a bounded finite R-module cochain
map f : K → L, its jth tensor component sends [e,x] to [e,f^j(x)]. The coefficient and outer
S-action remain fixed. -/
theorem bimoduleTensor_map_mk {K L : Bounded (FGModuleCat.{u} R)}
    (f : K ⟶ L) (j : ℤ) (e : E) (x : K.obj.X j) :
    letI : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
    letI : Module ℤ (L.obj.X j) := Module.compHom (L.obj.X j) (algebraMap ℤ R)
    (((bimoduleTensor (S := S) E).map f).hom.f j).hom.hom
        (TensorProduct.Balanced.mk ℤ R E (K.obj.X j) e x) =
      TensorProduct.Balanced.mk ℤ R E (L.obj.X j) e ((f.hom.f j).hom.hom x) := by
  let : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
  let : Module ℤ (L.obj.X j) := Module.compHom (L.obj.X j) (algebraMap ℤ R)
  exact FGModuleCat.bimoduleTensor_map_mk (R := R) (S := S) E (f.hom.f j) e x

/-- Let R,S be rings and E a commuting left-S/right-R bimodule finite over S. There is a natural
isomorphism between bounded tensoring by E followed by fgModuleAmbient S and fgModuleAmbient R
followed by the ambient cochain tensor functor. Both routes have the same balanced tensor
terms and module maps. -/
def bimoduleTensorAmbientIso :
    bimoduleTensor (R := R) (S := S) E ⋙ fgModuleAmbient S ≅
      fgModuleAmbient R ⋙ ModuleCat.bimoduleTensorCochain (S := S) E := Iso.refl _

/-- For a commuting left-S/right-R bimodule E finite over S, K ∈ Bounded(FGModuleCat R), and j ∈
ℤ, the jth component of bimoduleTensorAmbientIso(E).hom is the identity of the ambient module
E⊗_R K^j. -/
theorem bimoduleTensorAmbientIso_hom_app_f (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorAmbientIso (S := S) E).hom.app K).f j =
      𝟙 ((ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj ((K.obj.X j).obj)) := rfl

section RightFlat

variable (hE : ∀ N : ModuleCat.{u} R,
  IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))

include hE

/-- Let R,S,E share universe u, with E a commuting left-S/right-R bimodule finite over S. Assume
Tor₁^R(E,N)=0 for every N ∈ ModuleCat.{u} R. For K ∈ Bounded(FGModuleCat.{u} R) and j ∈ ℤ, the
ambient tensor complex has an isomorphism H^j(U_S(E⊗K)) ≅ E⊗_R H^j(U_RK), where U_R,U_S forget
finite generation and boundedness. -/
def bimoduleTensorAmbientHomologyIso (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((fgModuleAmbient S).obj ((bimoduleTensor (S := S) E).obj K)).homology j ≅
      (ModuleCat.BalancedTensor.Left.functor ℤ R S E).obj
        (((fgModuleAmbient R).obj K).homology j) :=
  ModuleCat.bimoduleTensorCochainHomologyIso E hE ((fgModuleAmbient R).obj K) j

/-- For rings R,S and a commuting left-S/right-R bimodule E finite over S in universe u, assume
Tor₁^R(E,N)=0 for every N ∈ ModuleCat.{u} R. For a bounded finite-module cochain map f : K → L
and j ∈ ℤ, the comparison maps e satisfy H^j(U_S(E⊗f))≫e_L.hom=e_K.hom≫(E⊗H^j(U_Rf)). The
homology is computed in the ambient module categories. -/
theorem bimoduleTensorAmbientHomologyIso_hom_naturality
    {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L) (j : ℤ) :
    HomologicalComplex.homologyMap
        ((fgModuleAmbient S).map ((bimoduleTensor (S := S) E).map f)) j ≫
        (bimoduleTensorAmbientHomologyIso E hE L j).hom =
      (bimoduleTensorAmbientHomologyIso E hE K j).hom ≫
        (ModuleCat.BalancedTensor.Left.functor ℤ R S E).map
          (HomologicalComplex.homologyMap ((fgModuleAmbient R).map f) j) :=
  ModuleCat.bimoduleTensorCochainHomologyIso_hom_naturality E hE
    ((fgModuleAmbient R).map f) j

/-- Let R,S,E share universe u, with E a commuting left-S/right-R bimodule finite over S and
Tor₁^R(E,N)=0 for every left R-module N of that universe. If f : K → L between bounded finite
R-module cochains is an ambient quasi-isomorphism, then its tensor image is an ambient
quasi-isomorphism of S-module cochains. -/
theorem bimoduleTensor_ambientQuasiIso {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L)
    (hf : QuasiIso ((fgModuleAmbient R).map f)) :
    QuasiIso ((fgModuleAmbient S).map ((bimoduleTensor (S := S) E).map f)) := by
  let : QuasiIso ((fgModuleAmbient R).map f) := hf
  exact ModuleCat.bimoduleTensorCochain_quasiIso E hE ((fgModuleAmbient R).map f)

/-- For a commuting left-S/right-R bimodule E finite over S in universe u and with Tor₁^R(E,N)=0
for every N ∈ ModuleCat.{u} R, the bounded tensor functor sends every morphism in
fgModuleQuasiIsomorphisms R into fgModuleQuasiIsomorphisms S. This is the inverse-image
containment for those two ambient morphism properties. -/
theorem bimoduleTensor_map_quasiIsomorphisms :
    fgModuleQuasiIsomorphisms R ≤
      (fgModuleQuasiIsomorphisms S).inverseImage (bimoduleTensor (S := S) E) := by
  intro K L f hf
  exact bimoduleTensor_ambientQuasiIso E hE f hf

end RightFlat

end CochainComplex.Bounded

namespace CochainComplex.Bounded

variable (R : Type u) [Ring R]

/-- For a ring R in universe u, tensoring by the regular (R,R)-bimodule R on
Bounded(FGModuleCat.{u} R) is naturally isomorphic to the identity functor. The degreewise
comparison is the regular balanced tensor unitor R⊗_R K^j ≅ K^j. -/
def bimoduleTensorRegularIso :
    bimoduleTensor (R := R) (S := R) R ≅ 𝟭 (Bounded (FGModuleCat.{u} R)) :=
  NatIso.mapCochainComplexBounded (FGModuleCat.bimoduleTensorUnitNatIso R) ≪≫
    Functor.mapCochainComplexBoundedIdIso

/-- Let R be a ring, K ∈ Bounded(FGModuleCat.{u} R), and j ∈ ℤ. The jth forward component of the
regular bounded tensor isomorphism equals the finite-module unitor R⊗_R K^j → K^j. -/
theorem bimoduleTensorRegularIso_hom_app_f (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorRegularIso R).hom.app K).hom.f j =
      (FGModuleCat.bimoduleTensorUnitIso R (K.obj.X j)).hom := by
  simp [bimoduleTensorRegularIso, Functor.mapCochainComplexBoundedIdIso,
    NatIso.mapCochainComplexBounded, NatTrans.mapCochainComplexBounded,
    FGModuleCat.bimoduleTensorUnitNatIso]

/-- For a ring R, a bounded finite R-module cochain complex K, j ∈ ℤ, r ∈ R, and x ∈ K^j, the
forward regular coefficient isomorphism sends [r,x] to r·x. The tensor is balanced over the
possibly noncommutative ring R. -/
theorem bimoduleTensorRegularIso_mk (K : Bounded (FGModuleCat.{u} R)) (j : ℤ)
    (r : R) (x : K.obj.X j) :
    letI : Module ℤ R := AddCommGroup.toIntModule R
    letI : Module ℤ (K.obj.X j) := Module.compHom (K.obj.X j) (algebraMap ℤ R)
    (((bimoduleTensorRegularIso R).hom.app K).hom.f j).hom.hom
        (TensorProduct.Balanced.mk ℤ R R (K.obj.X j) r x) = r • x := by
  rw [bimoduleTensorRegularIso_hom_app_f]
  exact FGModuleCat.bimoduleTensorUnitIso_mk R (K.obj.X j) r x

variable {R}
variable {S : Type u} [Ring S]
  {E E' : Type u} [AddCommGroup E] [AddCommGroup E']
  [Module S E] [Module S E'] [Module Rᵐᵒᵖ E] [Module Rᵐᵒᵖ E']
  [SMulCommClass S Rᵐᵒᵖ E] [SMulCommClass S Rᵐᵒᵖ E']
  [Module.Finite S E] [Module.Finite S E']

/-- Let R,S be rings and E,E′ commuting left-S/right-R bimodules finite over S. If f : E →ₗ[S] E′
satisfies f(e·r)=f(e)·r for all r,e, then it induces a natural transformation between the
bounded finite-module tensor functors for E and E′. Its degree-j component sends [e,x] to
[f(e),x]. -/
def bimoduleTensorTransformation (f : E →ₗ[S] E')
    (hR : ∀ (r : R) (e : E), f (MulOpposite.op r • e) = MulOpposite.op r • f e) :
    bimoduleTensor (R := R) (S := S) E ⟶ bimoduleTensor (R := R) (S := S) E' :=
  NatTrans.mapCochainComplexBounded (FGModuleCat.bimoduleTensorTransformation f hR)

/-- Let R,S be rings, E,E′ commuting left-S/right-R bimodules finite as S-modules, and f : E →ₗ[S]
E′ respect the right R-action. The jth component of its bounded transformation at K equals the
finite-module balanced coefficient map for K^j, with value [e,x] ↦ [f(e),x]. -/
theorem bimoduleTensorTransformation_app_f (f : E →ₗ[S] E')
    (hR : ∀ (r : R) (e : E), f (MulOpposite.op r • e) = MulOpposite.op r • f e)
    (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorTransformation f hR).app K).hom.f j =
      FGModuleCat.bimoduleTensorCoefficientComponent f hR (K.obj.X j) := rfl

/-- Let R,S be rings and E,E′ commuting left-S/right-R bimodules finite over S. An S-linear
equivalence e : E ≃ₗ[S] E′ commuting with the right R-action induces a natural isomorphism
between their bounded finite-module tensor functors. The forward and inverse maps apply e and
e⁻¹ to the coefficient factor. -/
def bimoduleTensorCoefficientIso (e : E ≃ₗ[S] E')
    (hR : ∀ (r : R) (x : E), e (MulOpposite.op r • x) = MulOpposite.op r • e x) :
    bimoduleTensor (R := R) (S := S) E ≅ bimoduleTensor (R := R) (S := S) E' :=
  NatIso.mapCochainComplexBounded (FGModuleCat.bimoduleTensorIso e hR)

/-- For rings R,S, commuting left-S/right-R bimodules E,E′ finite as S-modules, and an S-linear
equivalence e respecting the right R-action, the degree-j forward component of the bounded
coefficient isomorphism at K equals the finite-module coefficient isomorphism at K^j. It sends
[x,m] to [e(x),m]. -/
theorem bimoduleTensorCoefficientIso_hom_app_f (e : E ≃ₗ[S] E')
    (hR : ∀ (r : R) (x : E), e (MulOpposite.op r • x) = MulOpposite.op r • e x)
    (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorCoefficientIso e hR).hom.app K).hom.f j =
      (FGModuleCat.bimoduleTensorIso e hR).hom.app (K.obj.X j) := rfl

end CochainComplex.Bounded

namespace CochainComplex.Bounded

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]
  (E F : Type u) [AddCommGroup E] [AddCommGroup F]
  [Module S E] [Module Rᵐᵒᵖ E] [SMulCommClass S Rᵐᵒᵖ E] [Module.Finite S E]
  [Module T F] [Module Sᵐᵒᵖ F] [SMulCommClass T Sᵐᵒᵖ F] [Module.Finite T F]

/-- Let R,S,T be rings in universe u, E a commuting left-S/right-R bimodule finite over S, and F a
commuting left-T/right-S bimodule finite over T. The composite coefficient F⊗_S E is a
left-T/right-R bimodule finite over T. Tensoring by it gives Bounded(FGModuleCat R) →
Bounded(FGModuleCat T). -/
abbrev bimoduleTensorComposite : Bounded (FGModuleCat.{u} R) ⥤ Bounded (FGModuleCat.{u} T) :=
  Functor.mapCochainComplexBounded
    (FGModuleCat.bimoduleTensorCompositeFunctor (R := R) (S := S) (T := T) E F)

/-- For rings R,S,T, a left-S/right-R bimodule E finite over S, and a left-T/right-S bimodule F
finite over T, there is a natural isomorphism from the bounded tensor functor of F⊗_S E to
tensoring first by E and then by F. Its degreewise map is the associator (F⊗_S E)⊗_R K^j ≅
F⊗_S(E⊗_R K^j), preserving the order F,E,K. -/
def bimoduleTensorCompIso :
    bimoduleTensorComposite (R := R) (S := S) (T := T) E F ≅
      bimoduleTensor (R := R) (S := S) E ⋙ bimoduleTensor (R := S) (S := T) F :=
  NatIso.mapCochainComplexBounded
    (FGModuleCat.bimoduleTensorCompNatIso (R := R) (S := S) (T := T) E F) ≪≫
      (Functor.mapCochainComplexBoundedCompIso
        (FGModuleCat.bimoduleTensor (R := R) (S := S) E)
        (FGModuleCat.bimoduleTensor (R := S) (S := T) F)).symm

/-- Let R,S,T be rings, E a commuting left-S/right-R bimodule finite over S, and F a commuting
left-T/right-S bimodule finite over T. For K ∈ Bounded(FGModuleCat R) and j ∈ ℤ, the forward
component of bimoduleTensorCompIso(E,F) is the finite-module associator (F⊗_S E)⊗_R K^j →
F⊗_S(E⊗_R K^j). -/
theorem bimoduleTensorCompIso_hom_app_f (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorCompIso (R := R) (S := S) (T := T) E F).hom.app K).hom.f j =
      (FGModuleCat.bimoduleTensorCompIso (R := R) (S := S) (T := T) E F (K.obj.X j)).hom := by
  simp [bimoduleTensorCompIso, Functor.mapCochainComplexBoundedCompIso,
    NatIso.mapCochainComplexBounded, NatTrans.mapCochainComplexBounded,
    FGModuleCat.bimoduleTensorCompNatIso]

end CochainComplex.Bounded

namespace CochainComplex.Bounded

variable (R S P Q : Type u) [Ring R] [Ring S]
  [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (a : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (ha : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    ∀ (r : R) (x : TensorProduct.Balanced ℤ S P Q), a (r • x) = r * a x)
  (b : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hb : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    ∀ (s : S) (x : TensorProduct.Balanced ℤ R Q P), b (s • x) = s * b x)

local notation "e₀" => ModuleCat.bimoduleTensorMoritaEquivalence R S P Q a ha b hb

/-- Let R,S be rings in universe u, P a commuting left-R/right-S bimodule, and Q a commuting
left-S/right-R bimodule. Suppose a : P⊗_S Q ≃ R and b : Q⊗_R P ≃ S are equivalences preserving
both endpoint actions. Their module Morita equivalence restricts to Bounded(FGModuleCat.{u} R)
≌ Bounded(FGModuleCat.{u} S). The forward functor is Q⊗_R− and the inverse is P⊗_S−; the
contractions give the required finite generation. -/
def bimoduleTensorMoritaEquivalence :
    Bounded (FGModuleCat.{u} R) ≌ Bounded (FGModuleCat.{u} S) :=
  (e₀).fgModuleCatEquivalence.mapCochainComplexBounded

/-- For rings R,S and commuting bimodules P_(R,S), Q_(S,R) with bimodule equivalences P⊗_S Q≃R and
Q⊗_R P≃S, the forward functor of the induced bounded finite-module Morita equivalence equals
the bounded tensor functor Q⊗_R−. Its left-S finiteness is obtained from the contraction data. -/
theorem bimoduleTensorMoritaEquivalence_functor :
    (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).functor =
      letI := (ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb).2.1
      bimoduleTensor (R := R) (S := S) Q := rfl

/-- Let P_(R,S), Q_(S,R) be commuting bimodules over rings R,S, with bimodule equivalences P⊗_S
Q≃R and Q⊗_R P≃S. The inverse bounded finite-module Morita functor is P⊗_S−. The required
left-R finiteness of P is obtained from these contraction data. -/
theorem bimoduleTensorMoritaEquivalence_inverse :
    (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).inverse =
      letI := (ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb).1
      bimoduleTensor (R := S) (S := R) P := rfl

/-- Let R,S be rings and P_(R,S),Q_(S,R) commuting bimodules with specified bimodule equivalences
P⊗_S Q≃R and Q⊗_R P≃S. Let e₀ be their induced finite-module tensor equivalence. At K ∈
Bounded(FGModuleCat R) and j ∈ ℤ, the bounded unit component equals e₀.unit at K^j : K^j →
P⊗_S(Q⊗_R K^j). -/
theorem bimoduleTensorMoritaEquivalence_unitIso_hom_app_f
    (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    ((bimoduleTensorMoritaEquivalence R S P Q a ha b hb).unitIso.hom.app K).hom.f j =
      (e₀).fgModuleCatEquivalence.unitIso.hom.app (K.obj.X j) :=
  Equivalence.mapCochainComplexBounded_unitIso_hom_app_f _ K j

/-- Let P_(R,S), Q_(S,R) be commuting bimodules with bimodule equivalences P⊗_S Q≃R and Q⊗_R P≃S.
For K ∈ Bounded(FGModuleCat S) and j ∈ ℤ, the bounded Morita counit equals the finite-module
tensor-equivalence counit at K^j, with source Q⊗_R(P⊗_S K^j) and target K^j. -/
theorem bimoduleTensorMoritaEquivalence_counitIso_hom_app_f
    (K : Bounded (FGModuleCat.{u} S)) (j : ℤ) :
    ((bimoduleTensorMoritaEquivalence R S P Q a ha b hb).counitIso.hom.app K).hom.f j =
      (e₀).fgModuleCatEquivalence.counitIso.hom.app (K.obj.X j) :=
  Equivalence.mapCochainComplexBounded_counitIso_hom_app_f _ K j

/-- For rings R,S and commuting bimodules P_(R,S),Q_(S,R) with specified bimodule equivalences
P⊗_S Q≃R and Q⊗_R P≃S, let K ∈ Bounded(FGModuleCat R) and j ∈ ℤ. Forgetting finite generation
and boundedness from the degree-j unit gives the ambient module-equivalence unit at K^j, with
target P⊗_S(Q⊗_R K^j). -/
theorem bimoduleTensorMoritaEquivalence_unitIso_module
    (K : Bounded (FGModuleCat.{u} R)) (j : ℤ) :
    (((bimoduleTensorMoritaEquivalence R S P Q a ha b hb).unitIso.hom.app K).hom.f j).hom =
      (e₀).eqv.unitIso.hom.app ((K.obj.X j).obj) := by
  rw [bimoduleTensorMoritaEquivalence_unitIso_hom_app_f]
  rfl

/-- Let R,S be rings and P_(R,S), Q_(S,R) a commuting bimodule pair with contractions P⊗_S Q≃R and
Q⊗_R P≃S. For K ∈ Bounded(FGModuleCat S) and j ∈ ℤ, the underlying degree-j bounded counit is
the ambient module-equivalence counit Q⊗_R(P⊗_S K^j) → K^j. -/
theorem bimoduleTensorMoritaEquivalence_counitIso_module
    (K : Bounded (FGModuleCat.{u} S)) (j : ℤ) :
    (((bimoduleTensorMoritaEquivalence R S P Q a ha b hb).counitIso.hom.app K).hom.f j).hom =
      (e₀).eqv.counitIso.hom.app ((K.obj.X j).obj) := by
  rw [bimoduleTensorMoritaEquivalence_counitIso_hom_app_f]
  rfl

/-- For rings R,S and commuting bimodules P_(R,S), Q_(S,R) with bimodule equivalences P⊗_S Q≃R and
Q⊗_R P≃S, the bounded Morita forward functor Q⊗_R− sends fgModuleQuasiIsomorphisms R to
fgModuleQuasiIsomorphisms S. These properties test homology in the ambient module cochain
categories, so the statement applies without an abelian finite-module category hypothesis. -/
theorem bimoduleTensorMoritaEquivalence_map_quasiIsomorphisms :
    fgModuleQuasiIsomorphisms R ≤ (fgModuleQuasiIsomorphisms S).inverseImage
      (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).functor := by
  let H := ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb
  let : Module.Finite S Q := H.2.1
  exact bimoduleTensor_map_quasiIsomorphisms (R := R) (S := S) Q H.2.2.2

/-- Let R,S be rings and P_(R,S), Q_(S,R) commuting bimodules with contractions P⊗_S Q≃R and Q⊗_R
P≃S preserving both endpoint actions. The inverse bounded tensor functor P⊗_S− sends every
ambient quasi-isomorphism of bounded finite S-module cochains to an ambient quasi-isomorphism
of bounded finite R-module cochains. -/
theorem bimoduleTensorMoritaEquivalence_inverse_map_quasiIsomorphisms :
    fgModuleQuasiIsomorphisms S ≤ (fgModuleQuasiIsomorphisms R).inverseImage
      (bimoduleTensorMoritaEquivalence R S P Q a ha b hb).inverse := by
  let H := ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb
  let : Module.Finite R P := H.1
  exact bimoduleTensor_map_quasiIsomorphisms (R := S) (S := R) P H.2.2.1

end CochainComplex.Bounded

end
