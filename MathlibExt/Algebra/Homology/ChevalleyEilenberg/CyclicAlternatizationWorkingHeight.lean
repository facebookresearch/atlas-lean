/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesWorkingHeight
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicAlternatization

/-!
# Cyclic exterior maps in a common module universe

For a k-algebra ring A, form its Connes quotient complex at height h = max u v z. The tensor
representative is obtained by the first-factor tensor decomposition, the carrier lift and the
quotient projection. It equals the base Connes representative followed by the module lift and
the canonical isomorphism from the lifted quotient complex to the quotient formed at height h.

Full signed permutation alternation induces an integral map ⋀[k]^(n+1) A → Cλ_h(A)_n. For a
ℚ-algebra k, normalization uses 1/(n + 1), and the degree-signed variant also uses (−1)^n.
These maps are the corresponding base maps followed by the same lift comparison.

For A and B in independent carrier universes and a nonunital k-algebra map f, all
representative and exterior-map squares commute at the common height max u v w z.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct BigOperators

universe u v w z

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ, connesConsUpAtHeight is the k-linear map A
⊗[k] TensorPower k n A → (cyclicBicomplexAtHeight k A).X 0.X n with value x ↦ ULift.up x. -/
def connesConsUpAtHeight (n : ℕ) : (A ⊗[k] TensorPower k n A) →ₗ[k]
    ((ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexAtHeight.{u,v,z} k A).X 0).X n :=
  { toFun := ULift.up
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ and x : A ⊗[k] TensorPower k n A,
connesConsUpAtHeight k A n x = ULift.up x in the first-column bicomplex term at height h. -/
theorem connesConsUpAtHeight_apply (n : ℕ) (x : A ⊗[k] TensorPower k n A) :
    connesConsUpAtHeight.{u,v,z} k A n x = ULift.up x := rfl

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ, connesTermUpAtHeight is the k-linear
carrier lift Cλ(A)_n → ULift(Cλ(A)_n), the degree-n term of the complex obtained by applying
ModuleCat.uliftFunctor from max u v to h. Its value is the inverse of the module up/down
equivalence. -/
def connesTermUpAtHeight (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A).X n →ₗ[k]
      (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).X n :=
  (ULift.moduleEquiv :
    (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).X n ≃ₗ[k]
        (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A).X n).symm.toLinearMap

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ, connesTensorRepresentativeAtHeight :
TensorPower k (n + 1) A →ₗ[k] Cλ_h(A)_n first applies (TensorPower.consEquiv k A n).symm, then
connesConsUpAtHeight, then connesProjectionAtHeight. -/
def connesTensorRepresentativeAtHeight (n : ℕ) :
    TensorPower k (n + 1) A →ₗ[k]
      (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  ((ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight.{u,v,z} k A n).hom).comp
    ((connesConsUpAtHeight.{u,v,z} k A n).comp (TensorPower.consEquiv k A n).symm.toLinearMap)

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Write U_n : Cλ(A)_n → ULift(Cλ(A)_n) for
connesTermUpAtHeight and J_n : ULift(Cλ(A)_n) ≃ Cλ_h(A)_n for the component of the canonical
Connes lift comparison. For x : TensorPower k (n + 1) A, q_h(x) = J_n.hom(U_n(q_base(x))),
where q_base is connesTensorRepresentative in the base universe. -/
theorem connesTensorRepresentativeAtHeight_image (n : ℕ) (x : TensorPower k (n + 1) A) :
    connesTensorRepresentativeAtHeight.{u,v,z} k A n x =
      ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom
        (connesTermUpAtHeight.{u,v,z} k A n
          (ModuleCat.Algebra.Hochschild.Matrix.connesTensorRepresentative k A n x)) := by
  let E := HomologicalComplex.eval (ModuleCat.{max u v z} k) (ComplexShape.down ℕ) n
  have hπ := E.congr_map
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight_π.{u,v,z} k A)
  simp only [E, Functor.map_comp, HomologicalComplex.eval_map, HomologicalComplex.eval_obj,
    HomologicalComplex.comp_f] at hπ
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hπ)
    (connesConsUpAtHeight.{u,v,z} k A n ((TensorPower.consEquiv k A n).symm x))
  change ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom
      (connesTermUpAtHeight.{u,v,z} k A n
        (ModuleCat.Algebra.Hochschild.Matrix.connesTensorRepresentative k A n x)) =
    connesTensorRepresentativeAtHeight.{u,v,z} k A n x at h
  exact h.symm

variable {B : Type w} [Ring B] [Algebra k B]

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Let B : Type w be another k-algebra ring and f : A
→ₙₐ[k] B a nonunital k-algebra map. Use the common height H = max u v w z and let Cλ_H(f) be
the induced map between the two quotient complexes. For n : ℕ and x : TensorPower k (n + 1) A,
Cλ_H(f)_n(q_H^A(x)) = q_H^B(PiTensorProduct.map (fun _ => f) x). Thus every tensor factor is
mapped by f. -/
theorem connesTensorRepresentativeAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ)
    (x : TensorPower k (n + 1) A) :
    ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom
        (connesTensorRepresentativeAtHeight.{u,v,max u v w z} k A n x) =
      connesTensorRepresentativeAtHeight.{u,w,max u v w z} k B n
        (PiTensorProduct.map (fun _ : Fin (n + 1) => (f : A →ₗ[k] B)) x) := by
  let a := (TensorPower.consEquiv k A n).symm x
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight_naturality.{u,v,w,z} k A f n))
      (connesConsUpAtHeight.{u,v,max u v w z} k A n a)
  change ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom
      ((ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight.{u,v,max u v w z} k A n).hom
        (connesConsUpAtHeight.{u,v,max u v w z} k A n a)) =
    (ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight.{u,w,max u v w z} k B n).hom
      ((((ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexMapAtHeight.{u,v,w,z} f).f 0).f n).hom
        (connesConsUpAtHeight.{u,v,max u v w z} k A n a)) at h
  have hm : (((ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexMapAtHeight.{u,v,w,z} f).f 0).f n).hom
      (connesConsUpAtHeight.{u,v,max u v w z} k A n a) =
    connesConsUpAtHeight.{u,w,max u v w z} k B n (TensorPower.consLevelMap (f : A →ₗ[k] B) n a) :=
      by
        rw [connesConsUpAtHeight_apply, connesConsUpAtHeight_apply]
        exact ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexMapAtHeight_f_f_up.{u,v,w,z} f 0 n a
  rw [hm] at h
  have hc := LinearMap.congr_fun (TensorPower.consEquiv_naturality (f : A →ₗ[k] B) n) a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
  dsimp only [a] at hc
  rw [LinearEquiv.apply_symm_apply] at hc
  have hc' := congrArg (TensorPower.consEquiv k B n).symm hc
  simp only [LinearEquiv.symm_apply_apply] at hc'
  let qB := ModuleCat.Algebra.Hochschild.NonUnital.connesProjectionAtHeight.{u,w,max u v w z} k B n
  exact h.trans (congrArg
    (fun y => qB.hom (connesConsUpAtHeight.{u,w,max u v w z} k B n y)) hc')

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ, cyclicFullAlternatingAtHeight is the
alternating map on Fin (n + 1) obtained from q_h ∘ PiTensorProduct.tprod k by full signed
permutation alternation. -/
def cyclicFullAlternatingAtHeight (n : ℕ) :
    A [⋀^Fin (n + 1)]→ₗ[k]
      (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  ((connesTensorRepresentativeAtHeight.{u,v,z} k A n).compMultilinearMap
    (PiTensorProduct.tprod k)).alternatization

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For n : ℕ, cyclicFullExteriorAtHeight : ⋀[k]^(n+1) A
→ₗ[k] Cλ_h(A)_n is the linear map corresponding to cyclicFullAlternatingAtHeight, with all
signed permutation terms included. -/
def cyclicFullExteriorAtHeight (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k]
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  exteriorPower.alternatingMapLinearEquiv (cyclicFullAlternatingAtHeight.{u,v,z} k A n)

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. For a : Fin (n + 1) → A, cyclicFullExteriorAtHeight n
(ιMulti a) = ∑ σ : Perm(Fin(n+1)), sign(σ) • q_h(tprod(a ∘ σ)). The tuple is reindexed by σ
itself. -/
theorem cyclicFullExteriorAtHeight_pure (n : ℕ) (a : Fin (n + 1) → A) :
    cyclicFullExteriorAtHeight.{u,v,z} k A n (exteriorPower.ιMulti k (n + 1) a) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), σ.sign • connesTensorRepresentativeAtHeight.{u,v,z} k A n
        (PiTensorProduct.tprod k (a ∘ σ)) := by
  rw [cyclicFullExteriorAtHeight, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    cyclicFullAlternatingAtHeight, MultilinearMap.alternatization_apply]
  rfl

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Write U_n : Cλ(A)_n → ULift(Cλ(A)_n) for
connesTermUpAtHeight and J_n : ULift(Cλ(A)_n) ≃ Cλ_h(A)_n for the component of the canonical
Connes lift comparison. For every n : ℕ, cyclicFullExteriorAtHeight n = J_n.hom ∘ U_n ∘
cyclicFullExterior n as k-linear maps from ⋀[k]^(n+1) A to Cλ_h(A)_n. -/
theorem cyclicFullExteriorAtHeight_image (n : ℕ) :
    cyclicFullExteriorAtHeight.{u,v,z} k A n =
      (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom).comp
        ((connesTermUpAtHeight.{u,v,z} k A n).comp (cyclicFullExterior k A n)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change cyclicFullExteriorAtHeight.{u,v,z} k A n (exteriorPower.ιMulti k (n + 1) a) =
    ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom
      (connesTermUpAtHeight.{u,v,z} k A n (cyclicFullExterior k A n (exteriorPower.ιMulti k (n + 1) a)))
  rw [cyclicFullExteriorAtHeight_pure, cyclicFullExterior_pure, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul_unit, map_zsmul_unit]
  exact congrArg (fun y => σ.sign • y)
    (connesTensorRepresentativeAtHeight_image.{u,v,z} k A n (PiTensorProduct.tprod k (a ∘ σ)))

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Let B : Type w be another k-algebra ring and f : A
→ₙₐ[k] B a nonunital k-algebra map. Use the common height H = max u v w z and let Cλ_H(f) be
the induced map between the two quotient complexes. For n : ℕ, Cλ_H(f)_n ∘
cyclicFullExteriorAtHeight_A(n) = cyclicFullExteriorAtHeight_B(n) ∘ ⋀^(n+1) f. -/
theorem cyclicFullExteriorAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom).comp
        (cyclicFullExteriorAtHeight.{u,v,max u v w z} k A n) =
      (cyclicFullExteriorAtHeight.{u,w,max u v w z} k B n).comp
        (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom
      (cyclicFullExteriorAtHeight.{u,v,max u v w z} k A n (exteriorPower.ιMulti k (n + 1) a)) =
    cyclicFullExteriorAtHeight.{u,w,max u v w z} k B n
      (exteriorPower.map (n + 1) (f : A →ₗ[k] B) (exteriorPower.ιMulti k (n + 1) a))
  rw [exteriorPower.map_apply_ιMulti, cyclicFullExteriorAtHeight_pure, cyclicFullExteriorAtHeight_pure, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul_unit]
  have h := connesTensorRepresentativeAtHeight_naturality.{u,v,w,z} k A f n
    (PiTensorProduct.tprod k (a ∘ σ))
  simp only [PiTensorProduct.map_tprod] at h
  exact congrArg (fun y => σ.sign • y) h

section Rational

variable [Algebra ℚ k]

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Assume k is a ℚ-algebra. For n : ℕ,
cyclicExteriorAtHeight is algebraMap ℚ k ((n + 1 : ℚ)⁻¹) times cyclicFullExteriorAtHeight :
⋀[k]^(n+1) A →ₗ[k] Cλ_h(A)_n. -/
def cyclicExteriorAtHeight (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k]
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  algebraMap ℚ k ((n + 1 : ℚ)⁻¹) • cyclicFullExteriorAtHeight.{u,v,z} k A n

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Write U_n : Cλ(A)_n → ULift(Cλ(A)_n) for
connesTermUpAtHeight and J_n : ULift(Cλ(A)_n) ≃ Cλ_h(A)_n for the component of the canonical
Connes lift comparison. If k is a ℚ-algebra, cyclicExteriorAtHeight n = J_n.hom ∘ U_n ∘
cyclicExterior n for every n : ℕ. Both normalized maps use the factor 1/(n + 1). -/
theorem cyclicExteriorAtHeight_image (n : ℕ) :
    cyclicExteriorAtHeight.{u,v,z} k A n =
      (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom).comp
        ((connesTermUpAtHeight.{u,v,z} k A n).comp (cyclicExterior k A n)) := by
  rw [cyclicExteriorAtHeight, cyclicExterior, cyclicFullExteriorAtHeight_image,
    LinearMap.comp_smul, LinearMap.comp_smul]

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Assume k is a ℚ-algebra. Let B : Type w be another
k-algebra ring and f : A →ₙₐ[k] B a nonunital k-algebra map. Use the common height H = max u v
w z and let Cλ_H(f) be the induced map between the two quotient complexes. For n : ℕ,
Cλ_H(f)_n ∘ cyclicExteriorAtHeight_A(n) = cyclicExteriorAtHeight_B(n) ∘ ⋀^(n+1) f. -/
theorem cyclicExteriorAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom).comp
        (cyclicExteriorAtHeight.{u,v,max u v w z} k A n) =
      (cyclicExteriorAtHeight.{u,w,max u v w z} k B n).comp
        (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  rw [cyclicExteriorAtHeight, cyclicExteriorAtHeight, LinearMap.comp_smul, LinearMap.smul_comp,
    cyclicFullExteriorAtHeight_naturality]

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Assume k is a ℚ-algebra. For n : ℕ,
cyclicExteriorWeibelAtHeight : ⋀[k]^(n+1) A →ₗ[k] Cλ_h(A)_n equals (−1 : k)^n times
cyclicExteriorAtHeight n. -/
def cyclicExteriorWeibelAtHeight (n : ℕ) : (⋀[k]^(n + 1) A) →ₗ[k]
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
  (-1 : k) ^ n • cyclicExteriorAtHeight.{u,v,z} k A n

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Write U_n : Cλ(A)_n → ULift(Cλ(A)_n) for
connesTermUpAtHeight and J_n : ULift(Cλ(A)_n) ≃ Cλ_h(A)_n for the component of the canonical
Connes lift comparison. If k is a ℚ-algebra, cyclicExteriorWeibelAtHeight n = J_n.hom ∘ U_n ∘
cyclicExteriorWeibel n. Both maps retain the degree factor (−1)^n. -/
theorem cyclicExteriorWeibelAtHeight_image (n : ℕ) :
    cyclicExteriorWeibelAtHeight.{u,v,z} k A n =
      (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom.f n).hom).comp
        ((connesTermUpAtHeight.{u,v,z} k A n).comp (cyclicExteriorWeibel k A n)) := by
  rw [cyclicExteriorWeibelAtHeight, cyclicExteriorWeibel, cyclicExteriorAtHeight_image,
    LinearMap.comp_smul, LinearMap.comp_smul]

/-- Let k : Type u be a commutative ring and A : Type v a k-algebra ring. For a spare universe z,
put h = max u v z, let Cλ_h(A) be the Connes quotient complex formed in ModuleCat.{h} k, and
let q_h be its whole-tensor projection. Assume k is a ℚ-algebra. Let B : Type w be another
k-algebra ring and f : A →ₙₐ[k] B a nonunital k-algebra map. Use the common height H = max u v
w z and let Cλ_H(f) be the induced map between the two quotient complexes. For n : ℕ,
Cλ_H(f)_n ∘ cyclicExteriorWeibelAtHeight_A(n) = cyclicExteriorWeibelAtHeight_B(n) ∘ ⋀^(n+1) f. -/
theorem cyclicExteriorWeibelAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A f).f n).hom).comp
        (cyclicExteriorWeibelAtHeight.{u,v,max u v w z} k A n) =
      (cyclicExteriorWeibelAtHeight.{u,w,max u v w z} k B n).comp
        (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) := by
  rw [cyclicExteriorWeibelAtHeight, cyclicExteriorWeibelAtHeight, LinearMap.comp_smul, LinearMap.smul_comp,
    cyclicExteriorAtHeight_naturality]

end Rational
end ChevalleyEilenberg
