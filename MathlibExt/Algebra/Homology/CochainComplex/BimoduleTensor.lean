/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGModuleCat.BimoduleTensor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Cochain tensoring by a noncommutative bimodule

Let R,S be rings and E a left S-module and right R-module with commuting actions. The balanced
tensor E⊗_R− extends degreewise to integer cochain complexes. Its terms carry the outer
S-action, its differential sends [e,x] to [e,dx], and cochain maps act on the second factor.
The raw construction allows independent ring, bimodule, and input carrier universes.

In the common-universe setting R,S,E : Type u, vanishing of the balanced Tor₁^R(E,N) for every
N ∈ ModuleCat.{u} R gives preservation of homology. The resulting comparison H^j(E⊗K) ≅
E⊗H^j(K) is natural, and tensoring preserves quasi-isomorphisms at each degree and globally.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uR uS uE uM u

attribute [local instance] ModuleCat.BalancedTensor.Left.additive

namespace ModuleCat

section OriginalCarriers

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
  (E : Type uE) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E]

/-- Let R,S be rings, E a left S-module and right R-module whose actions commute, and K an integer
cochain complex of left R-modules. Apply E⊗_R− degreewise to define a functor to integer
cochain complexes of left S-modules. For E in universe uE and input terms in uM, the output
has universe max(uE,uM), independently of the ring universes. The S-action is s·[e,x]=[s·e,x]. -/
abbrev bimoduleTensorCochain :
    CochainComplex (ModuleCat.{uM} R) ℤ ⥤
      CochainComplex (ModuleCat.{max uE uM} S) ℤ :=
  (BalancedTensor.Left.functor ℤ R S E).mapHomologicalComplex (.up ℤ)

/-- For rings R,S, a commuting left-S/right-R bimodule E, an integer cochain complex K of
R-modules, and j ∈ ℤ, the jth term of bimoduleTensorCochain(E)(K) is exactly the balanced
left-module tensor functor applied to K^j. Its carrier is E⊗_R K^j with the outer S-action. -/
theorem bimoduleTensorCochain_obj_X (K : CochainComplex (ModuleCat.{uM} R) ℤ) (j : ℤ) :
    ((bimoduleTensorCochain (S := S) E).obj K).X j =
      (BalancedTensor.Left.functor ℤ R S E).obj (K.X j) := rfl

/-- Let R,S be rings, E a commuting left-S/right-R bimodule, and K an integer cochain complex of
R-modules. For i,j ∈ ℤ, the differential of E⊗_R K from i to j equals the balanced tensor
functor applied to d_K^{i,j}. Thus it acts on the second factor and retains the coefficient E. -/
theorem bimoduleTensorCochain_obj_d (K : CochainComplex (ModuleCat.{uM} R) ℤ) (i j : ℤ) :
    ((bimoduleTensorCochain (S := S) E).obj K).d i j =
      (BalancedTensor.Left.functor ℤ R S E).map (K.d i j) := rfl

/-- For a commuting left-S/right-R bimodule E over rings R,S and a cochain map f : K → L of
integer R-module complexes, the jth component of E⊗_R f is the balanced tensor functor applied
to f^j. This is an S-linear map E⊗_R K^j → E⊗_R L^j. -/
theorem bimoduleTensorCochain_map_f {K L : CochainComplex (ModuleCat.{uM} R) ℤ}
    (f : K ⟶ L) (j : ℤ) :
    ((bimoduleTensorCochain (S := S) E).map f).f j =
      (BalancedTensor.Left.functor ℤ R S E).map (f.f j) := rfl

/-- Let R,S be rings, E a commuting left-S/right-R bimodule, K an integer R-module cochain
complex, i,j ∈ ℤ, e ∈ E, and x ∈ K^i. The differential sends the balanced class [e,x] to
[e,d_K^{i,j}(x)]. The balancing is over R and the ground additive tensor is over ℤ. -/
theorem bimoduleTensorCochain_d_mk (K : CochainComplex (ModuleCat.{uM} R) ℤ)
    (i j : ℤ) (e : E) (x : K.X i) :
    letI : Module ℤ (K.X i) := Module.compHom (K.X i) (algebraMap ℤ R)
    letI : Module ℤ (K.X j) := Module.compHom (K.X j) (algebraMap ℤ R)
    (((bimoduleTensorCochain (S := S) E).obj K).d i j).hom
        (TensorProduct.Balanced.mk ℤ R E (K.X i) e x) =
      TensorProduct.Balanced.mk ℤ R E (K.X j) e ((K.d i j).hom x) := by
  let : Module ℤ (K.X i) := Module.compHom (K.X i) (algebraMap ℤ R)
  let : Module ℤ (K.X j) := Module.compHom (K.X j) (algebraMap ℤ R)
  exact BalancedTensor.Left.map_mk ℤ R S E (K.d i j) e x

/-- For rings R,S, a commuting left-S/right-R bimodule E, and a cochain map f : K → L, the jth
tensor component sends [e,x] ∈ E⊗_R K^j to [e,f^j(x)] ∈ E⊗_R L^j. The left S-action remains on
the coefficient E. -/
theorem bimoduleTensorCochain_map_mk {K L : CochainComplex (ModuleCat.{uM} R) ℤ}
    (f : K ⟶ L) (j : ℤ) (e : E) (x : K.X j) :
    letI : Module ℤ (K.X j) := Module.compHom (K.X j) (algebraMap ℤ R)
    letI : Module ℤ (L.X j) := Module.compHom (L.X j) (algebraMap ℤ R)
    (((bimoduleTensorCochain (S := S) E).map f).f j).hom
        (TensorProduct.Balanced.mk ℤ R E (K.X j) e x) =
      TensorProduct.Balanced.mk ℤ R E (L.X j) e ((f.f j).hom x) := by
  let : Module ℤ (K.X j) := Module.compHom (K.X j) (algebraMap ℤ R)
  let : Module ℤ (L.X j) := Module.compHom (L.X j) (algebraMap ℤ R)
  exact BalancedTensor.Left.map_mk ℤ R S E (f.f j) e x

/-- Let R,S be rings and E a commuting left-S/right-R bimodule. The image of the zero integer
R-module cochain complex under E⊗_R− is a zero object in the S-module cochain category. This
follows from the additive balanced tensor functor and requires no flatness condition. -/
theorem bimoduleTensorCochain_zero :
    IsZero ((bimoduleTensorCochain (R := R) (S := S) E).obj
      (0 : CochainComplex (ModuleCat.{uM} R) ℤ)) :=
  (bimoduleTensorCochain (R := R) (S := S) E).map_isZero (isZero_zero _)

end OriginalCarriers

section RightFlat

variable {R S : Type u} [Ring R] [Ring S]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E]
  (hE : ∀ N : ModuleCat.{u} R,
    IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))

include hE

/-- Let R,S,E have carrier universe u, with R,S rings and E a commuting left-S/right-R bimodule.
Suppose the balanced Tor object (torFirst R 1)(E,N) is zero for every N ∈ ModuleCat.{u} R.
Then E⊗_R− : ModuleCat.{u} R → ModuleCat.{u} S preserves homology. The Tor₁ condition is on
the right R-module E, not its left S-action. -/
theorem bimoduleTensor_preservesHomology :
    (BalancedTensor.Left.functor ℤ R S E :
      ModuleCat.{u} R ⥤ ModuleCat.{u} S).PreservesHomology := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : PreservesFiniteLimits F := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteColimits F := bimoduleTensor_preservesFiniteColimits E
  infer_instance

/-- Let R,S be rings and E a commuting left-S/right-R bimodule, all in universe u. Assume
(torFirst R 1)(E,N)=0 for every N ∈ ModuleCat.{u} R. For an integer cochain complex K in
ModuleCat.{u} R and j ∈ ℤ, the canonical homology comparison is an isomorphism H^j(E⊗_R K) ≅
E⊗_R H^j(K) in ModuleCat.{u} S. -/
def bimoduleTensorCochainHomologyIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : ℤ) :
    ((bimoduleTensorCochain (S := S) E).obj K).homology j ≅
      (BalancedTensor.Left.functor ℤ R S E).obj (K.homology j) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.PreservesHomology := bimoduleTensor_preservesHomology E hE
  exact (K.sc j).mapHomologyIso F

/-- Let R,S be rings and E a commuting left-S/right-R bimodule, all in universe u, with
Tor₁^R(E,N)=0 for every N ∈ ModuleCat.{u} R. For a cochain map f : K → L and j ∈ ℤ, let e_K
and e_L be H^j(E⊗−) ≅ E⊗H^j(−). Then H^j(E⊗f) ≫ e_L.hom = e_K.hom ≫ (E⊗H^j(f)). This is an
equality of S-module maps. -/
theorem bimoduleTensorCochainHomologyIso_hom_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (j : ℤ) :
    HomologicalComplex.homologyMap ((bimoduleTensorCochain (S := S) E).map f) j ≫
        (bimoduleTensorCochainHomologyIso E hE L j).hom =
      (bimoduleTensorCochainHomologyIso E hE K j).hom ≫
        (BalancedTensor.Left.functor ℤ R S E).map (HomologicalComplex.homologyMap f j) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.PreservesHomology := bimoduleTensor_preservesHomology E hE
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) j).map f) F

/-- For rings R,S and a commuting left-S/right-R bimodule E in universe u, suppose Tor₁^R(E,N)=0
for every N ∈ ModuleCat.{u} R. If a map f : K → L of integer R-module cochain complexes is a
quasi-isomorphism at j, then E⊗_R f is a quasi-isomorphism at j in S-modules. The homology
comparison identifies its map with E⊗H^j(f). -/
theorem bimoduleTensorCochain_quasiIsoAt
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (j : ℤ) [QuasiIsoAt f j] :
    QuasiIsoAt ((bimoduleTensorCochain (S := S) E).map f) j := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.PreservesHomology := bimoduleTensor_preservesHomology E hE
  exact HomologicalComplex.quasiIsoAt_map_of_preservesHomology f F j

/-- Let R,S,E share universe u, with R,S rings and E a commuting left-S/right-R bimodule. Assume
Tor₁^R(E,N)=0 for every N ∈ ModuleCat.{u} R. If f : K → L is a quasi-isomorphism of integer
R-module cochain complexes, then the degreewise map E⊗_R f is a quasi-isomorphism of S-module
cochain complexes in every integer degree. -/
theorem bimoduleTensorCochain_quasiIso
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((bimoduleTensorCochain (S := S) E).map f) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : F.PreservesHomology := bimoduleTensor_preservesHomology E hE
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f F

end RightFlat

end ModuleCat

end
