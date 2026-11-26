/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.LieModuleCat.Restriction
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientFunctor

/-!
# CE chains under Lie algebra and coefficient maps

Fix a commutative ring R. A Lie homomorphism f : L → L' and a coefficient map g : M → f* N
intertwining the L-action with the restricted L'-action define an ambient tensor map
ExteriorAlgebra.map f ⊗ g. It commutes with the diagonal actions, exterior insertion and the
coefficient boundaries. In degree n the map is ⋀^n f ⊗ g, and it commutes with the homogeneous
CE differentials.

The linear operator statements allow separate source and target Lie-algebra and coefficient
universes. Bundled chain maps use common Lie and coefficient carrier universes. For an
L'-module N, taking g to be the identity gives CE(L,f* N) → CE(L',N); these restriction maps
are natural in N and compose with Lie homomorphisms.

See Weibel, *An Introduction to Homological Algebra*, Chapter 7.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v v' w w'

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

section LinearNaturality

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L')
variable (M : LieModuleCat.{w} R L) (N : LieModuleCat.{w'} R L')

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. Define
coefficientLieAmbientMap : ExteriorAlgebra R L ⊗[R] M →ₗ[R] ExteriorAlgebra R L' ⊗[R] N as
ExteriorAlgebra.map f tensored with g. It sends a ⊗ m to ExteriorAlgebra.map f(a) ⊗ g(m). -/
def coefficientLieAmbientMap (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) :
    (ExteriorAlgebra R L ⊗[R] M) →ₗ[R] (ExteriorAlgebra R L' ⊗[R] N) :=
  TensorProduct.map (ExteriorAlgebra.map f.toLinearMap).toLinearMap g.toLinearMap

@[simp]
theorem coefficientLieAmbientMap_tmul
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N)
    (a : ExteriorAlgebra R L) (m : M) :
    coefficientLieAmbientMap R L f M N g (a ⊗ₜ[R] m) =
      ExteriorAlgebra.map f.toLinearMap a ⊗ₜ[R] g m := by
  simp only [coefficientLieAmbientMap, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, LieModuleHom.coe_toLinearMap]

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. Let F be the ambient
exterior tensor map. For x : L, F ∘ coefficientDiagonalAction_(L,M)(x) =
coefficientDiagonalAction_(L',N)(f(x)) ∘ F. The diagonal actions combine the exterior adjoint
and coefficient actions. -/
theorem coefficientLieDiagonalAction_naturality
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (x : L) :
    (coefficientLieAmbientMap R L f M N g).comp
        (coefficientDiagonalAction R L M x) =
      (coefficientDiagonalAction R L' N (f x)).comp
        (coefficientLieAmbientMap R L f M N g) := by
  have haction (a : ExteriorAlgebra R L) :
      ExteriorAlgebra.map f.toLinearMap (adjointAction R L x a) =
        adjointAction R L' (f x) (ExteriorAlgebra.map f.toLinearMap a) :=
    LinearMap.congr_fun (adjointAction_naturality R L f x) a
  have hg (m : M) : g ⁅x, m⁆ = (⁅f x, g m⁆ : N) := by
    simpa only [LieModuleCat.restrictObj_lie] using g.map_lie x m
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, coefficientDiagonalAction_tmul, map_add,
    coefficientLieAmbientMap_tmul, haction, hg]

theorem coefficientLieDiagonalAction_naturality_apply
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (x : L)
    (p : ExteriorAlgebra R L ⊗[R] M) :
    coefficientLieAmbientMap R L f M N g (coefficientDiagonalAction R L M x p) =
      coefficientDiagonalAction R L' N (f x)
        (coefficientLieAmbientMap R L f M N g p) :=
  LinearMap.congr_fun (coefficientLieDiagonalAction_naturality R L f M N g x) p

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. For x : L, the ambient map F
satisfies F ∘ coefficientInsertion_(L,M)(x) = coefficientInsertion_(L',N)(f(x)) ∘ F, where
insertion multiplies the exterior factor on the left by its generator. -/
theorem coefficientLieInsertion_naturality
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (x : L) :
    (coefficientLieAmbientMap R L f M N g).comp (coefficientInsertion R L M x) =
      (coefficientInsertion R L' N (f x)).comp
        (coefficientLieAmbientMap R L f M N g) := by
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, coefficientInsertion_tmul,
    coefficientLieAmbientMap_tmul, map_mul, ExteriorAlgebra.map_apply_ι,
    LieHom.coe_toLinearMap]

theorem coefficientLieInsertion_naturality_apply
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (x : L)
    (p : ExteriorAlgebra R L ⊗[R] M) :
    coefficientLieAmbientMap R L f M N g (coefficientInsertion R L M x p) =
      coefficientInsertion R L' N (f x) (coefficientLieAmbientMap R L f M N g p) :=
  LinearMap.congr_fun (coefficientLieInsertion_naturality R L f M N g x) p

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. The ambient map F =
ExteriorAlgebra.map f ⊗ g satisfies F ∘ coefficientBoundary R L M = coefficientBoundary R L' N
∘ F. -/
theorem coefficientLieBoundary_naturality
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) :
    (coefficientLieAmbientMap R L f M N g).comp (coefficientBoundary R L M) =
      (coefficientBoundary R L' N).comp (coefficientLieAmbientMap R L f M N g) := by
  apply TensorProduct.ext'
  intro a m
  change coefficientLieAmbientMap R L f M N g
      (coefficientBoundary R L M (a ⊗ₜ[R] m)) =
    coefficientBoundary R L' N
      (coefficientLieAmbientMap R L f M N g (a ⊗ₜ[R] m))
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [coefficientBoundary_algebraMap_tmul, map_zero,
        coefficientLieAmbientMap_tmul, AlgHom.commutes,
        coefficientBoundary_algebraMap_tmul]
  | add a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [coefficientLieAmbientMap_tmul, map_mul,
        ExteriorAlgebra.map_apply_ι, LieHom.coe_toLinearMap] at ha ⊢
      rw [coefficientBoundary_ι_mul_tmul, coefficientBoundary_ι_mul_tmul,
        map_sub, map_neg, coefficientLieDiagonalAction_naturality_apply,
        coefficientLieInsertion_naturality_apply, ha]
      simp only [coefficientLieAmbientMap_tmul]

theorem coefficientLieBoundary_naturality_apply
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N)
    (p : ExteriorAlgebra R L ⊗[R] M) :
    coefficientLieAmbientMap R L f M N g (coefficientBoundary R L M p) =
      coefficientBoundary R L' N (coefficientLieAmbientMap R L f M N g p) :=
  LinearMap.congr_fun (coefficientLieBoundary_naturality R L f M N g) p

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. For n : ℕ,
coefficientLieDegreeMap is ⋀[R]^n L ⊗[R] M →ₗ[R] ⋀[R]^n L' ⊗[R] N given by TensorProduct.map
(exteriorPower.map n f.toLinearMap) g.toLinearMap. Its value on a ⊗ m is ⋀^n f(a) ⊗ g(m). -/
def coefficientLieDegreeMap
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ) :
    ((⋀[R]^n L) ⊗[R] M) →ₗ[R] ((⋀[R]^n L') ⊗[R] N) :=
  TensorProduct.map (exteriorPower.map n f.toLinearMap) g.toLinearMap

@[simp]
theorem coefficientLieDegreeMap_tmul
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ)
    (a : ⋀[R]^n L) (m : M) :
    coefficientLieDegreeMap R L f M N g n (a ⊗ₜ[R] m) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] g m := by
  simp only [coefficientLieDegreeMap, TensorProduct.map_tmul,
    LieModuleHom.coe_toLinearMap]

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. Let F_n =
coefficientLieDegreeMap n, F the ambient map, and J_n, J'_n the homogeneous tensor inclusions.
For every n : ℕ, J'_n ∘ F_n = F ∘ J_n. -/
theorem coefficientLieDegreeMap_inclusion
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ) :
    ((⋀[R]^n L').subtype.rTensor N).comp (coefficientLieDegreeMap R L f M N g n) =
      (coefficientLieAmbientMap R L f M N g).comp ((⋀[R]^n L).subtype.rTensor M) := by
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, coefficientLieDegreeMap_tmul,
    LinearMap.rTensor_tmul, Submodule.subtype_apply, exteriorPower.coe_map,
    coefficientLieAmbientMap_tmul]

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. For n : ℕ, the homogeneous
degree maps F_n satisfy F_n ∘ coefficientDifferential_(L,M)(n) =
coefficientDifferential_(L',N)(n) ∘ F_(n+1). The source and target Lie and coefficient
carriers may have different universes. -/
theorem coefficientLieDifferential_naturality
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ) :
    (coefficientLieDegreeMap R L f M N g n).comp (coefficientDifferential R L M n) =
      (coefficientDifferential R L' N n).comp
        (coefficientLieDegreeMap R L f M N g (n + 1)) := by
  have hinclusion (k : ℕ) (p : (⋀[R]^k L) ⊗[R] M) :=
    LinearMap.congr_fun (coefficientLieDegreeMap_inclusion R L f M N g k) p
  simp only [LinearMap.comp_apply] at hinclusion
  apply LinearMap.ext
  intro p
  apply DirectSum.subtype_rTensor_injective (fun k : ℕ => ⋀[R]^k L') N n
  change ((⋀[R]^n L').subtype.rTensor N)
      (coefficientLieDegreeMap R L f M N g n (coefficientDifferential R L M n p)) =
    ((⋀[R]^n L').subtype.rTensor N)
      (coefficientDifferential R L' N n (coefficientLieDegreeMap R L f M N g (n + 1) p))
  rw [hinclusion, coefficientDifferential_inclusion_apply,
    coefficientDifferential_inclusion_apply, hinclusion]
  exact coefficientLieBoundary_naturality_apply R L f M N g
    (((⋀[R]^(n + 1) L).subtype.rTensor M) p)

end LinearNaturality

section NativeMaps

variable {L' L'' : Type v}
variable [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
variable (f : L →ₗ⁅R⁆ L')
variable (M : LieModuleCat.{w} R L) (N : LieModuleCat.{w} R L')

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. For the bundled complexes, L
and L' have the same carrier universe v and M and N the same carrier universe w, with chain
terms in ModuleCat.{max u v w} R. The maps F_n = ⋀^n f ⊗ g assemble into
coefficientLieComplexMap : coefficientComplex R L M ⟶ coefficientComplex R L' N. Its degree-n
component sends a ⊗ m to ⋀^n f(a) ⊗ g(m). -/
def coefficientLieComplexMap (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) :
    coefficientComplex R L M ⟶ coefficientComplex R L' N :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (coefficientLieDegreeMap R L f M N g n))
    (fun n => by
      simp only [coefficientComplex_d_succ]
      exact congrArg ModuleCat.ofHom
        (coefficientLieDifferential_naturality R L f M N g n).symm)

@[simp]
theorem coefficientLieComplexMap_f
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ) :
    (coefficientLieComplexMap R L f M N g).f n =
      ModuleCat.ofHom (coefficientLieDegreeMap R L f M N g n) := rfl

theorem coefficientLieComplexMap_f_tmul
    (g : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f N) (n : ℕ)
    (a : ⋀[R]^n L) (m : M) :
    ((coefficientLieComplexMap R L f M N g).f n).hom (a ⊗ₜ[R] m) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] g m :=
  coefficientLieDegreeMap_tmul R L f M N g n a m

/-- Let R : Type u be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism between carrier-universe-v
algebras, and N an L'-module with carrier universe w. The map coefficientRestrictionMap goes
from coefficientComplex R L (f* N) to coefficientComplex R L' N. In degree n it is ⋀^n f ⊗
id_N. -/
def coefficientRestrictionMap :
    coefficientComplex R L (LieModuleCat.restrictObj f N) ⟶ coefficientComplex R L' N :=
  coefficientLieComplexMap R L f (LieModuleCat.restrictObj f N) N LieModuleHom.id

theorem coefficientRestrictionMap_f_tmul (n : ℕ) (a : ⋀[R]^n L) (m : N) :
    ((coefficientRestrictionMap R L f N).f n).hom (a ⊗ₜ[R] m) =
      exteriorPower.map n f.toLinearMap a ⊗ₜ[R] m := by
  rw [coefficientRestrictionMap, coefficientLieComplexMap_f_tmul, LieModuleHom.id_apply]

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism in a common Lie carrier universe, and
g : N ⟶ P a morphism of L'-modules in a common coefficient universe. Then restriction_N
followed by coefficientComplexMap g equals coefficientComplexMap (restrictMap f g) followed by
restriction_P, as maps CE(L,f* N) → CE(L',P). -/
theorem coefficientRestrictionMap_naturality
    {P : LieModuleCat.{w} R L'} (g : N ⟶ P) :
    coefficientRestrictionMap R L f N ≫ coefficientComplexMap R L' N g =
      coefficientComplexMap R L (LieModuleCat.restrictObj f N)
        (LieModuleCat.restrictMap f g) ≫ coefficientRestrictionMap R L f P := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a m
  change ((coefficientComplexMap R L' N g).f n).hom
      (((coefficientRestrictionMap R L f N).f n).hom (a ⊗ₜ[R] m)) =
    ((coefficientRestrictionMap R L f P).f n).hom
      (((coefficientComplexMap R L (LieModuleCat.restrictObj f N)
        (LieModuleCat.restrictMap f g)).f n).hom (a ⊗ₜ[R] m))
  rw [coefficientRestrictionMap_f_tmul, coefficientComplexMap_f_tmul,
    coefficientComplexMap_f_tmul, coefficientRestrictionMap_f_tmul]
  rfl

/-- Let R : Type u be commutative and f : L →ₗ⁅R⁆ L' a Lie homomorphism with both Lie carriers in
universe v. For coefficient universe w, the maps CE(L,f* N) → CE(L',N) form a natural
transformation LieModuleCat.restrict f ⋙ coefficientComplexFunctor R L ⟶
coefficientComplexFunctor R L', with degree-n component ⋀^n f ⊗ id_N. -/
def coefficientRestrictionNatTrans :
    LieModuleCat.restrict f ⋙ coefficientComplexFunctor R L ⟶
      coefficientComplexFunctor R L' where
  app N := coefficientRestrictionMap R L f N
  naturality N P g := (coefficientRestrictionMap_naturality R L f N g).symm

/-- Let R be commutative, f : L →ₗ⁅R⁆ L' and h : L' →ₗ⁅R⁆ L'' Lie homomorphisms in the same Lie
carrier universe, and P an L''-module. The restriction map CE(L,f*(h*P)) → CE(L',h*P) followed
by CE(L',h*P) → CE(L'',P) equals coefficientRestrictionMap for h.comp f. In every degree the
exterior maps compose and the coefficient factor remains the identity. -/
theorem coefficientRestrictionMap_comp (h : L' →ₗ⁅R⁆ L'')
    (P : LieModuleCat.{w} R L'') :
    coefficientRestrictionMap R L f (LieModuleCat.restrictObj h P) ≫
        coefficientRestrictionMap R L' h P =
      coefficientRestrictionMap R L (h.comp f) P := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a m
  change ((coefficientRestrictionMap R L' h P).f n).hom
      (((coefficientRestrictionMap R L f (LieModuleCat.restrictObj h P)).f n).hom
        (a ⊗ₜ[R] m)) =
    ((coefficientRestrictionMap R L (h.comp f) P).f n).hom (a ⊗ₜ[R] m)
  rw [coefficientRestrictionMap_f_tmul, coefficientRestrictionMap_f_tmul,
    coefficientRestrictionMap_f_tmul, LieHom.toLinearMap_comp,
    exteriorPower.map_comp, LinearMap.comp_apply]

end NativeMaps

end ChevalleyEilenberg
