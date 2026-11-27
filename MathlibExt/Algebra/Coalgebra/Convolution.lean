/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/Algebra/Coalgebra/Convolution.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Ideal.Operations
public import MathlibExt.LinearAlgebra.TensorProduct.Basic

/-!
# Comultiplication as a convolution product

Let `C` be an `R`-algebra carrying a comultiplication. This file records that, for the convolution
product of linear maps `C →ₗ[R] C ⊗[R] C`, comultiplication is the convolution product of the two
canonical inclusions `c ↦ c ⊗ₜ 1` and `c ↦ 1 ⊗ₜ c` of `C` into its tensor square.

The file also provides the exterior convolution product `WithConv.mulTensor`: linear maps
out of modules `M` and `N`, valued in an algebra, applied legwise on `M ⊗[R] N` and
multiplied in the codomain. Its normalization rules (zero, addition, scalars) and its
multiplicativity for the convolution product make it the engine for composition-level
convolution calculations: convolution products interleave legwise, and composing with a
multiplication lands in the image of `mulTensor` for maps with a suitable multiplicativity
law. This file proves that for an **algebra map**
(`AlgHom.toConv_toLinearMap_comp_mul'`); the Leibniz-rule counterpart for counit-valued
derivations is in `MathlibExt/Algebra/AlgebraicGroup/Tangent/Basic.lean`.

Finally, the file records how convolution algebras change with their coefficients. An algebra
map `g : B →ₐ[R] B'` induces Mathlib's `AlgHom.convPostcomp` on convolution algebras, and when
`B'` is a `B`-algebra with a basis over `B`, taking coordinates identifies the convolution
algebra with coefficients in `B'` with a free module over the one with coefficients in `B`.

Last, convolution products respect ideal-valued maps: the convolution product of maps with values
in ideals `I` and `J` of a commutative algebra has values in `I * J`, so the `n`-th convolution
power of a map with values in `I` has values in `I ^ n`. For a point `x = 1 + D` of an affine
group with `D` valued in `I`, this controls the binomial expansion of the powers of `x`.

For the convolution dual, the unit is the counit and multiplication is successive
contraction of comultiplication.

## Main declarations

* `LinearMap.ofConv_one_eq_counit`: the convolution-dual unit is the counit.
* `LinearMap.convMul_eq_comp_tensorComponent`: convolution-dual multiplication as contraction.
* `LinearMap.tensorComponent_lTensor_comul`: successive contractions on the right tensor factor.
* `MathlibExt.Coalgebra.comul_eq_convMul_includeLeft_includeRight`: comultiplication as the
  convolution product of the two tensor inclusions.
* `MathlibExt.Bialgebra.comulPoint_eq_include_mul`: the corresponding identity for the
  algebra-hom points of a commutative bialgebra.
* `MathlibExt.Bialgebra.toConv_comp_comulAlgHom`: the functorial form of the previous identity,
  after post-composing with an arbitrary algebra map out of the tensor square.
* `MathlibExt.Bialgebra.ofConv_one_eq_counitAlgHom`: the identity base-valued point is the counit.
* `WithConv.mulTensor`: the exterior convolution product, with its
  normalization rules and `WithConv.mulTensor_convMul`.
* `AlgHom.toConv_toLinearMap_comp_mul'`: an algebra map composed with
  multiplication is its own exterior square.
* `Module.Basis.convCoordEquiv`: the coordinates of a convolution-algebra element in a basis of
  the coefficients, with `Module.Basis.convCoordEquiv_convPostcomp_mul` recording that they are
  linear over the convolution algebra of the smaller coefficient ring.
* `LinearMap.convMul_apply_mem_mul` and `LinearMap.convPow_apply_mem_pow`: convolution products
  and powers of ideal-valued maps.
-/

public section

open TensorProduct WithConv

namespace LinearMap

variable {R C : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The unit of the convolution dual is the coalgebra counit. -/
@[simp]
theorem ofConv_one_eq_counit :
    (1 : WithConv (Module.Dual R C)).ofConv = Coalgebra.counit := by
  simp [convOne_def]

/-- Multiplication in the convolution dual is successive contraction of comultiplication. -/
theorem convMul_eq_comp_tensorComponent (f g : WithConv (Module.Dual R C)) :
    (f * g).ofConv = f.ofConv ∘ₗ tensorComponent g.ofConv ∘ₗ Coalgebra.comul := by
  have hp : f.ofConv ∘ₗ tensorComponent g.ofConv =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f.ofConv g.ofConv := by
    ext c d
    simp [mul_comm]
  rw [← comp_assoc, hp, convMul_def, comp_assoc]

/-- Successive contractions of a comultiplication on the right tensor factor are
contraction by the convolution product. -/
theorem tensorComponent_lTensor_comul {M : Type*} [AddCommMonoid M] [Module R M]
    (f g : WithConv (Module.Dual R C)) (x : M ⊗[R] C) :
    tensorComponent f.ofConv
        ((tensorComponent g.ofConv).lTensor M (Coalgebra.comul.lTensor M x)) =
      tensorComponent (f * g).ofConv x := by
  simp [lTensor_def, convMul_eq_comp_tensorComponent, comp_assoc]

end LinearMap

namespace MathlibExt

namespace Coalgebra

variable {R : Type*} {C : Type*} [CommSemiring R] [Semiring C] [Algebra R C]
  [_root_.CoalgebraStruct R C]

/-- **Comultiplication is the convolution product of the two tensor inclusions.** In the
convolution product on maps `C →ₗ[R] C ⊗[R] C`, the product of `includeLeft` and `includeRight`
multiplies the two legs of `Δ c` back together in order, which is `Δ` itself.

Only the comultiplication *data* is used, so this needs `CoalgebraStruct` rather than
`Coalgebra`: no coalgebra law, bialgebra compatibility or antipode axiom enters. -/
theorem comul_eq_convMul_includeLeft_includeRight :
    (toConv (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) : WithConv (C →ₗ[R] C ⊗[R] C)) =
      toConv (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap *
        toConv (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap := by
  apply WithConv.ofConv_injective
  have hmul : LinearMap.mul' R (C ⊗[R] C) ∘ₗ
      TensorProduct.map
        (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap
        (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap =
      LinearMap.id := by
    -- Mathlib's `lmul'_comp_map` requires a commutative target algebra, whereas `C ⊗[R] C`
    -- is only a semiring here. `lift_includeLeft_includeRight` computes the same pure tensors,
    -- but identifying this linear composite still requires tensor-product extensionality.
    apply TensorProduct.ext
    ext x y
    simp
  simp only [LinearMap.convMul_def]
  rw [← LinearMap.comp_assoc, hmul]
  simp

end Coalgebra

namespace Bialgebra

variable {R : Type*} [CommSemiring R]

section Semiring

variable {H : Type*} [Semiring H] [_root_.Bialgebra R H]

/-- **Post-composition splits the comultiplication point into its two inclusions.** For any
algebra map `φ` out of the tensor square, the point `φ ∘ Δ` is the convolution product of `φ`
restricted along the two inclusions.

The convolution monoid here is the one on points of `H` with values in the *commutative* algebra
`A`, so `H` itself need only be a semiring: the tensor square `H ⊗[R] H` is used solely as the
source of `φ`, never as a convolution target. That is why this is proved from the linear-map
identity `MathlibExt.Coalgebra.comul_eq_convMul_includeLeft_includeRight` rather than from
`MathlibExt.Bialgebra.comulPoint_eq_include_mul`, which needs `H ⊗[R] H` to be commutative. -/
theorem toConv_comp_comulAlgHom {A : Type*} [CommSemiring A] [Algebra R A]
    (phi : H ⊗[R] H →ₐ[R] A) :
    toConv (phi.comp (Bialgebra.comulAlgHom R H)) =
      toConv (phi.comp (Algebra.TensorProduct.includeLeft
        (R := R) (A := H) (B := H))) *
      toConv (phi.comp (Algebra.TensorProduct.includeRight
        (R := R) (A := H) (B := H))) := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul]
  have hcomul :
      (Bialgebra.comulAlgHom R H).toLinearMap =
        (toConv (Algebra.TensorProduct.includeLeft (R := R) (A := H) (B := H)).toLinearMap *
          toConv (Algebra.TensorProduct.includeRight
            (R := R) (A := H) (B := H)).toLinearMap).ofConv := by
    rw [← Coalgebra.comul_eq_convMul_includeLeft_includeRight (R := R) (C := H)]
    simp
  simp only [AlgHom.comp_toLinearMap, hcomul]
  exact congrArg WithConv.toConv (LinearMap.algHom_comp_convMul_distrib phi _ _)

/-- The identity of the convolution monoid of base-valued points `H →ₐ[R] R` is the counit. -/
theorem ofConv_one_eq_counitAlgHom :
    (1 : WithConv (H →ₐ[R] R)).ofConv = Bialgebra.counitAlgHom R H := by
  rw [AlgHom.convOne_def, ofConv_toConv, Algebra.ofId_self, AlgHom.id_comp]

end Semiring

variable {H : Type*} [CommSemiring H] [_root_.Bialgebra R H]

/-- The comultiplication point of a commutative bialgebra is the convolution product of the
two canonical tensor-factor points. This is the algebra-hom form of
`Coalgebra.comul_eq_convMul_includeLeft_includeRight`. -/
theorem comulPoint_eq_include_mul :
    toConv (Bialgebra.comulAlgHom R H) =
      toConv (Algebra.TensorProduct.includeLeft
        (R := R) (A := H) (B := H)) *
      toConv (Algebra.TensorProduct.includeRight
        (R := R) (A := H) (B := H)) := by
  simpa only [AlgHom.id_comp] using
    toConv_comp_comulAlgHom (phi := AlgHom.id R (H ⊗[R] H))

end Bialgebra

end MathlibExt

section ExteriorProduct

open WithConv TensorProduct

variable {R M N S : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Semiring S] [Algebra R S]

namespace WithConv

/-- The exterior convolution product on `M ⊗[R] N`: apply one factor on each tensor
leg and multiply the results in the coefficients. It underlies the Leibniz-rule
manipulations for counit-valued derivations: composing with the multiplication of the
bialgebra lands in this product's image (there at `N = M`). -/
def mulTensor (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    WithConv (M ⊗[R] N →ₗ[R] S) :=
  toConv (LinearMap.mul' R S ∘ₗ map s.ofConv t.ofConv)

/-- The exterior product evaluates a pure tensor legwise and multiplies the results
in the coefficients. -/
@[simp]
lemma mulTensor_apply_tmul
    (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) (x : M) (y : N) :
    (mulTensor s t).ofConv (x ⊗ₜ[R] y) = s.ofConv x * t.ofConv y := by
  simp [mulTensor]

/-- The exterior product vanishes when the left factor is zero. -/
@[simp]
lemma mulTensor_zero_left (t : WithConv (N →ₗ[R] S)) :
    mulTensor (0 : WithConv (M →ₗ[R] S)) t = 0 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- The exterior product vanishes when the right factor is zero. -/
@[simp]
lemma mulTensor_zero_right (s : WithConv (M →ₗ[R] S)) :
    mulTensor s (0 : WithConv (N →ₗ[R] S)) = 0 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- The exterior product is additive in the left factor. -/
@[simp]
lemma mulTensor_add_left (s₁ s₂ : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor (s₁ + s₂) t = mulTensor s₁ t + mulTensor s₂ t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [add_mul]

/-- The exterior product is additive in the right factor. -/
@[simp]
lemma mulTensor_add_right (s : WithConv (M →ₗ[R] S)) (t₁ t₂ : WithConv (N →ₗ[R] S)) :
    mulTensor s (t₁ + t₂) = mulTensor s t₁ + mulTensor s t₂ := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [mul_add]

/-- Scalars pull out of the left factor of the exterior product. -/
@[simp]
lemma mulTensor_smul_left (r : R) (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor (r • s) t = r • mulTensor s t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- Scalars pull out of the right factor of the exterior product. -/
@[simp]
lemma mulTensor_smul_right (r : R) (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor s (r • t) = r • mulTensor s t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

end WithConv

namespace AlgHom

variable {A : Type*} [Semiring A] [Algebra R A]

/-- An algebra-map point composed with multiplication is its own exterior square:
the multiplicativity of the point, in convolution form. -/
@[simp]
lemma toConv_toLinearMap_comp_mul' (g : A →ₐ[R] S) :
    toConv (g.toLinearMap ∘ₗ LinearMap.mul' R A) =
      mulTensor (toConv g.toLinearMap) (toConv g.toLinearMap) := by
  -- Not a re-derivation: this is Mathlib's `AlgHom.comp_mul'` transported into the file's
  -- own `mulTensor` vocabulary, which is what consumers rewrite with.
  exact congrArg toConv (AlgHom.comp_mul' g)

end AlgHom

end ExteriorProduct

section ExteriorConvolution

open WithConv TensorProduct

variable {R C D S : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
  [AddCommMonoid D] [Module R D] [CoalgebraStruct R D]
  [CommSemiring S] [Algebra R S]

namespace WithConv

/-- The exterior product is multiplicative for convolution: products interleave
legwise. Only the comultiplication *data* on each leg is used — no multiplication on the
sources and no bialgebra compatibility — so the two legs may be distinct coalgebras. -/
@[simp]
lemma mulTensor_convMul
    (s u : WithConv (C →ₗ[R] S)) (t v : WithConv (D →ₗ[R] S)) :
    mulTensor s t * mulTensor u v = mulTensor (s * u) (t * v) := by
  have h := LinearMap.algHom_comp_convMul_distrib
    (Algebra.TensorProduct.lmul' R (S := S))
    (toConv (map s.ofConv t.ofConv)) (toConv (map u.ofConv v.ofConv))
  -- The multiplication algebra map and the plain multiplication linear map agree;
  -- transport the resulting composition identity through the convolution type tag.
  rw [map_convMul_map, Algebra.TensorProduct.lmul'_toLinearMap] at h
  simpa only [mulTensor, ofConv_toConv, toConv_ofConv] using congrArg toConv h.symm

end WithConv

end ExteriorConvolution

section CoefficientChange

open WithConv

/-- A basis of `B'` over `B` identifies linear maps `C → B'` with families of linear maps
`C → B`, by taking coordinates. -/
noncomputable def _root_.Module.Basis.convCoordEquiv {ι B B' : Type*} [Finite ι]
    [Semiring B] [AddCommMonoid B'] [Module B B'] (b : Module.Basis ι B B') (R : Type*)
    [CommSemiring R] [Algebra R B] [Module R B'] [IsScalarTower R B B'] (C : Type*)
    [AddCommMonoid C] [Module R C] :
    WithConv (C →ₗ[R] B') ≃ₗ[R] (ι → WithConv (C →ₗ[R] B)) where
  toFun φ i := toConv ((b.coord i).restrictScalars R ∘ₗ φ.ofConv)
  invFun v := toConv ((b.equivFun.symm.toLinearMap.restrictScalars R) ∘ₗ
    _root_.LinearMap.pi fun i => (v i).ofConv)
  map_add' φ ψ := by ext; simp
  map_smul' r φ := by ext; simp
  left_inv φ := by
    ext c
    simp [LinearEquiv.symm_apply_eq, funext_iff]
  right_inv v := by
    ext i c
    simp [← Module.Basis.equivFun_apply]

section Basis

variable {ι B B' R C : Type*} [Finite ι] [CommSemiring R] [AddCommMonoid C] [Module R C]

section Module

variable [Semiring B] [AddCommMonoid B'] [Module B B'] [Algebra R B] [Module R B']
  [IsScalarTower R B B']

/-- The `i`-th component of `b.convCoordEquiv R C φ` is the `i`-th coordinate of `φ`. -/
@[simp]
theorem _root_.Module.Basis.convCoordEquiv_apply (b : Module.Basis ι B B')
    (φ : WithConv (C →ₗ[R] B')) (i : ι) :
    b.convCoordEquiv R C φ i = toConv ((b.coord i).restrictScalars R ∘ₗ φ.ofConv) :=
  (rfl)

/-- The inverse of `b.convCoordEquiv R C` reassembles a family of coordinate maps. -/
@[simp]
theorem _root_.Module.Basis.convCoordEquiv_symm_apply (b : Module.Basis ι B B')
    (v : ι → WithConv (C →ₗ[R] B)) :
    (b.convCoordEquiv R C).symm v =
      toConv ((b.equivFun.symm.toLinearMap.restrictScalars R) ∘ₗ
        _root_.LinearMap.pi fun i => (v i).ofConv) :=
  (rfl)

end Module

variable [CommSemiring B] [Semiring B'] [Algebra B B'] [Algebra R B] [Algebra R B']
  [IsScalarTower R B B']

/-- Taking coordinates in a basis of `B'` over `B` is linear over the convolution algebra with
coefficients in `B`, which acts on maps into `B'` through post-composition with
`algebraMap B B'`. -/
theorem _root_.Module.Basis.convCoordEquiv_convPostcomp_mul [_root_.Coalgebra R C]
    (b : Module.Basis ι B B') (f : WithConv (C →ₗ[R] B)) (φ : WithConv (C →ₗ[R] B')) (i : ι) :
    b.convCoordEquiv R C ((IsScalarTower.toAlgHom R B B').convPostcomp (C := C) f * φ) i =
      f * b.convCoordEquiv R C φ i := by
  ext c
  simp only [Module.Basis.convCoordEquiv_apply, AlgHom.convPostcomp_apply_ofConv,
    _root_.LinearMap.convMul_apply, _root_.LinearMap.comp_apply, ofConv_toConv]
  induction (CoalgebraStruct.comul c : C ⊗[R] C) with
  | tmul x y => simp [← Algebra.smul_def]
  | add x y hx hy => simp_all [map_add]

end Basis

end CoefficientChange

section IdealValued

open WithConv

namespace LinearMap

variable {R C A : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [CommSemiring A]
  [Algebra R A]

/-- The convolution product of a linear map with values in an ideal `I` and one with values in an
ideal `J` has values in `I * J`. -/
theorem convMul_apply_mem_mul [CoalgebraStruct R C] {I J : Ideal A} {f g : WithConv (C →ₗ[R] A)}
    (hf : ∀ c, f c ∈ I) (hg : ∀ c, g c ∈ J) (c : C) : (f * g) c ∈ I * J := by
  rw [convMul_apply]
  induction (CoalgebraStruct.comul c : C ⊗[R] C) with
  | tmul x y => simpa using Ideal.mul_mem_mul (hf x) (hg y)
  | add x y hx hy => simpa [map_add] using add_mem hx hy

/-- The `n`-th convolution power of a linear map with values in an ideal `I` has values in
`I ^ n`. -/
theorem convPow_apply_mem_pow [_root_.Coalgebra R C] {I : Ideal A} {f : WithConv (C →ₗ[R] A)}
    (hf : ∀ c, f c ∈ I) (n : ℕ) (c : C) : (f ^ n) c ∈ I ^ n := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => simpa [pow_succ] using convMul_apply_mem_mul ih hf c

end LinearMap

end IdealValued
