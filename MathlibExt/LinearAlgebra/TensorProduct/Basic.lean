/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/LinearAlgebra/TensorProduct/Basic.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor-product naturality, contractions and trace identities

This file records how tensor reassociation interacts with tensoring composite maps. It defines
contraction against a linear functional on the right factor, bundled as a linear map in the
functional, and records its behavior on pure tensors and under tensor-product maps.
Such contractions extract coordinates and test tensor identities, supporting componentwise
arguments about coactions and weight spaces. The file also proves the tensor identity that makes
the Casimir element of a trace commute with multiplication, and writes every tensor as a sum of
pure tensors over a finite spanning family of the right factor.

## Main declarations

* `LinearMap.assoc_rTensor_lTensor_comp`: reassociation commutes with tensoring a composite map.
* `LinearMap.lTensor_rTensor_comm`: tensoring maps on the two factors commutes elementwise.
* `LinearMap.rTensor_add_lTensor_comp_rTensor_comp_self`: the twisted co-Leibniz operator on
  `N ⊗ N` composed with itself, for an involution anticommuting with `b`.
* `LinearMap.injective_rTensor_congr`: injectivity of `f ⊗ 𝟙 M` is invariant under isomorphisms
  of `M`.
* `LinearMap.tensorComponent`: contraction against the right factor of a tensor product.
* `LinearMap.tensorComponentEquiv`: tensors as linear maps from the dual of a finite projective
  right factor.
* `LinearMap.sum_tensorComponent_tmul`: reconstruct a tensor from a dual family.
* `LinearMap.tensorComponent_eq_liftBaseChange`: contraction as scalar-linear extension.
* `LinearMap.tensorComponent_map`: naturality of contraction under `TensorProduct.map`.
* `LinearMap.tensorComponent_assoc_symm`: contraction commutes with reassociation.
* `LinearMap.comp_tensorComponent`: contraction commutes with a functional on the left.
* `LinearMap.tensorComponent_comp_tensorComponent`: successive contractions combine after
  reassociation.
* `LinearMap.tensorComponent_mul`: contracting a product in an algebra tensor product against a
  functional which splits on products splits the contraction accordingly.
* `LinearMap.rid_rTensor_apply`: naturality of the right tensor unitor.
* `LinearMap.sum_mul_tmul_eq_sum_tmul_mul`: the Casimir element of a trace commutes with
  multiplication.
* `TensorProduct.exists_eq_sum_tmul_of_span_eq_top`: over a finite spanning family of the right
  factor, every tensor is a sum of pure tensors with those right factors.
* `TensorProduct.nontrivial_right`: the right factor is nontrivial when the tensor product is.
* `TensorProduct.tensorTensorTensorComm_comm_tmul_comm`: exchanging the factors of both arguments
  of `tensorTensorTensorComm` exchanges the factors of its value.

## References

* L. Kadison, *New examples of Frobenius extensions*, University Lecture Series 14, AMS, 1999
  (dual bases of Frobenius algebras and extensions, and their Casimir elements).
-/

public section

open TensorProduct
open scoped TensorProduct

namespace LinearMap

universe u v w x y

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

section Naturality

variable {P Q S T : Type*}
variable [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
variable [AddCommMonoid S] [Module R S] [AddCommMonoid T] [Module R T]

/-- Reassociation commutes with tensoring a composite linear map and changing the last factor. -/
theorem assoc_rTensor_lTensor_comp (f : N →ₗ[R] P) (g : Q →ₗ[R] S)
    (ρ : M →ₗ[R] T ⊗[R] N) (t : M ⊗[R] Q) :
    TensorProduct.assoc R T P S ((f.lTensor T ∘ₗ ρ).rTensor S (g.lTensor M t)) =
      TensorProduct.map id (TensorProduct.map f g)
        (TensorProduct.assoc R T N Q (ρ.rTensor Q t)) := by
  simp only [lTensor_def, rTensor_map, comp_id]
  rw [← map_rTensor, ← TensorProduct.map_map_assoc]

/-- Tensoring maps on the two factors commutes, elementwise: `(𝟙 ⊗ g) ∘ (f ⊗ 𝟙)` and
`(f ⊗ 𝟙) ∘ (𝟙 ⊗ g)` agree on every element. -/
theorem lTensor_rTensor_comm (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    g.lTensor P (f.rTensor N x) = f.rTensor Q (g.lTensor M x) := by
  rw [← comp_apply, lTensor_comp_rTensor, ← rTensor_comp_lTensor, comp_apply]

/-- Injectivity of `f ⊗ 𝟙 M` only depends on `M` up to isomorphism. -/
theorem injective_rTensor_congr (f : N →ₗ[R] P) (e : M ≃ₗ[R] Q) :
    Function.Injective (f.rTensor M) ↔ Function.Injective (f.rTensor Q) := by
  have h : e.lTensor P ∘ f.rTensor M = f.rTensor Q ∘ e.lTensor N :=
    funext fun x ↦ lTensor_rTensor_comm f e.toLinearMap x
  rw [← EquivLike.comp_injective _ (e.lTensor P), h, EquivLike.injective_comp]

/-- Composing the twisted co-Leibniz operator `b ⊗ 𝟙 + (𝟙 ⊗ b) ∘ (τ ⊗ 𝟙)` on `N ⊗ N` with itself:
if `τ` is an involution anticommuting with `b`, the cross terms cancel and the composite is
`(b ∘ b) ⊗ 𝟙 + 𝟙 ⊗ (b ∘ b)`. -/
theorem rTensor_add_lTensor_comp_rTensor_comp_self (b τ : N →ₗ[R] N) (hτ : τ ∘ₗ τ = id)
    (hodd : b ∘ₗ τ + τ ∘ₗ b = 0) :
    (b.rTensor N + b.lTensor N ∘ₗ τ.rTensor N) ∘ₗ (b.rTensor N + b.lTensor N ∘ₗ τ.rTensor N) =
      (b ∘ₗ b).rTensor N + (b ∘ₗ b).lTensor N := by
  refine ext fun w ↦ ?_
  have hcross : TensorProduct.map (b ∘ₗ τ) b w + TensorProduct.map (τ ∘ₗ b) b w = 0 := by
    rw [← LinearMap.add_apply, ← TensorProduct.map_add_left, hodd, TensorProduct.map_zero_left,
      LinearMap.zero_apply]
  have hcommute (y : N ⊗[R] N) : τ.rTensor N (b.lTensor N y) = b.lTensor N (τ.rTensor N y) :=
    (lTensor_rTensor_comm τ b y).symm
  have hlast : b.lTensor N (τ.rTensor N (b.lTensor N (τ.rTensor N w))) = (b ∘ₗ b).lTensor N w := by
    rw [hcommute, ← lTensor_comp_apply, ← rTensor_comp_apply, hτ, rTensor_id_apply]
  have hcrossLeft :
      b.rTensor N (b.lTensor N (τ.rTensor N w)) = TensorProduct.map (b ∘ₗ τ) b w := by
    rw [← comp_apply, rTensor_comp_lTensor, map_rTensor]
  have hcrossRight :
      b.lTensor N (τ.rTensor N (b.rTensor N w)) = TensorProduct.map (τ ∘ₗ b) b w := by
    rw [← rTensor_comp_apply, ← comp_apply, lTensor_comp_rTensor]
  simp only [LinearMap.add_apply, comp_apply, map_add]
  rw [hcrossLeft, hcrossRight, hlast, ← rTensor_comp_apply]
  rw [show ∀ A B X Y : N ⊗[R] N, A + Y + (X + B) = A + B + (X + Y) from fun A B X Y ↦ by abel,
    hcross, add_zero]

end Naturality

/-- Apply a linear functional to the right factor of a tensor, linearly in the functional. -/
noncomputable def tensorComponent : (N →ₗ[R] R) →ₗ[R] M ⊗[R] N →ₗ[R] M :=
  (compRight R (TensorProduct.rid R M).toLinearMap).comp (lTensorHom M)

/-- Contraction is the tensor product of the functional with the identity, followed by the
right tensor unitor. -/
theorem tensorComponent_def (phi : N →ₗ[R] R) :
    tensorComponent (M := M) phi = (TensorProduct.rid R M).toLinearMap ∘ₗ phi.lTensor M := (rfl)

/-- A right tensor component sends a pure tensor to the corresponding scalar multiple. -/
@[simp]
theorem tensorComponent_tmul (phi : N →ₗ[R] R) (m : M) (n : N) :
    tensorComponent (R := R) (M := M) phi (m ⊗ₜ[R] n) = phi n • m := by
  simp [tensorComponent]

/-- For a finite projective right factor, contraction identifies tensors with linear maps
from its dual. This is `dualTensorHomEquiv` transported through `Module.evalEquiv` and
`TensorProduct.comm`. -/
noncomputable def tensorComponentEquiv [Module.Projective R N] [Module.Finite R N] :
    M ⊗[R] N ≃ₗ[R] (Module.Dual R N →ₗ[R] M) :=
  TensorProduct.comm R M N ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv R N) (.refl R M) ≪≫ₗ
    dualTensorHomEquiv R (Module.Dual R N) M

/-- Evaluating the tensor–dual-Hom equivalence is contraction against the given functional. -/
@[simp]
theorem tensorComponentEquiv_apply [Module.Projective R N] [Module.Finite R N]
    (x : M ⊗[R] N) (φ : Module.Dual R N) :
    tensorComponentEquiv x φ = tensorComponent φ x := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [tensorComponentEquiv]
  | add x y hx hy => simp [hx, hy]

/-- A family of vectors and functionals that reconstructs each vector also reconstructs
any tensor, by contracting its second factor. The family need not be linearly independent. -/
theorem sum_tensorComponent_tmul {ι : Type*} [Fintype ι]
    (b : ι → N) (φ : ι → N →ₗ[R] R)
    (hb : ∀ x, ∑ i, φ i x • b i = x) (z : M ⊗[R] N) :
    ∑ i, tensorComponent (φ i) z ⊗ₜ[R] b i = z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    simpa only [tensorComponent_tmul, smul_tmul, ← tmul_sum] using
      congrArg (fun n ↦ m ⊗ₜ[R] n) (hb n)
  | add z w hz hw => simp [add_tmul, Finset.sum_add_distrib, hz, hw]

/-- Over an algebra, contraction is the scalar-linear extension of the functional followed
by the algebra map. This expresses contraction as a linear map over the larger scalar ring. -/
theorem tensorComponent_eq_liftBaseChange {S : Type*} [CommSemiring S] [Algebra R S]
    (φ : N →ₗ[R] R) (z : S ⊗[R] N) :
    tensorComponent φ z = ((Algebra.linearMap R S).comp φ).liftBaseChange S z := by
  induction z using TensorProduct.inductionOn with
  | tmul s n => simp [Algebra.smul_def, mul_comm]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Taking a right tensor component commutes with a map on both tensor factors. -/
@[simp]
theorem tensorComponent_map {M' : Type x} {N' : Type y}
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (phi : N' →ₗ[R] R) (f : M →ₗ[R] M') (g : N →ₗ[R] N') (t : M ⊗[R] N) :
    tensorComponent phi (TensorProduct.map f g t) =
      f (tensorComponent (phi.comp g) t) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp

/-- Taking a right tensor component commutes with a map on the left factor. -/
@[simp]
theorem tensorComponent_rTensor {M' : Type x} [AddCommMonoid M'] [Module R M']
    (phi : N →ₗ[R] R) (f : M →ₗ[R] M') (t : M ⊗[R] N) :
    tensorComponent phi (f.rTensor N t) = f (tensorComponent phi t) := by
  simp [rTensor_def]

section

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Contraction of the last tensor factor commutes with reassociation. -/
@[simp]
theorem tensorComponent_assoc_symm (phi : P →ₗ[R] R) (u : M ⊗[R] (N ⊗[R] P)) :
    tensorComponent phi ((TensorProduct.assoc R M N P).symm u) =
      (tensorComponent phi).lTensor M u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul m v =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
    | tmul n p =>
      simp only [TensorProduct.assoc_symm_tmul, tensorComponent_tmul,
        lTensor_tmul, TensorProduct.tmul_smul]

/-- Contracting the middle factor after reassociation is contraction of the left factor of the
second tensor factor, followed by the left unitor. -/
@[simp]
theorem rTensor_tensorComponent_assoc_symm (phi : N →ₗ[R] R) (u : M ⊗[R] (N ⊗[R] P)) :
    (tensorComponent phi).rTensor P ((TensorProduct.assoc R M N P).symm u) =
      (TensorProduct.lid R P ∘ₗ phi.rTensor P).lTensor M u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul m v =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
    | tmul n p => simp [TensorProduct.smul_tmul]

/-- Applying two tensor components successively is contraction by the composed functional
on the last two factors, after reassociation. -/
theorem tensorComponent_comp_tensorComponent (phi : N →ₗ[R] R) (psi : P →ₗ[R] R) :
    tensorComponent (M := M) phi ∘ₗ tensorComponent (M := M ⊗[R] N) psi =
      tensorComponent (M := M) (phi ∘ₗ tensorComponent psi) ∘ₗ
        (TensorProduct.assoc R M N P).toLinearMap := by
  refine TensorProduct.ext_threefold fun m n p ↦ ?_
  simp [smul_smul]

/-- Applying functionals to both factors is independent of the order of contraction. -/
theorem comp_tensorComponent (psi : M →ₗ[R] R) (phi : N →ₗ[R] R) :
    psi ∘ₗ tensorComponent phi =
      phi ∘ₗ (TensorProduct.lid R N).toLinearMap ∘ₗ psi.rTensor N := by
  refine TensorProduct.ext' fun m n ↦ ?_
  simp only [comp_apply, tensorComponent_tmul, map_smul,
    smul_eq_mul, rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    mul_comm]

/-- Contracting the coefficient of a product in an algebra tensor product `A ⊗ C` against a
functional which splits on products as `θ (a * b) = φ a * ψ b + φ' a * ψ' b` splits the
contraction accordingly. For a comodule algebra this computes the contraction of the coaction of
a product. -/
theorem tensorComponent_mul {A C : Type*} [Semiring A] [Algebra R A] [Semiring C] [Algebra R C]
    {θ φ ψ φ' ψ' : C →ₗ[R] R} (hθ : ∀ a b, θ (a * b) = φ a * ψ b + φ' a * ψ' b)
    (x y : A ⊗[R] C) :
    tensorComponent θ (x * y) =
      tensorComponent φ x * tensorComponent ψ y + tensorComponent φ' x * tensorComponent ψ' y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [add_mul, map_add, hx, hx']
    abel
  | tmul a c =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [mul_add, map_add, hy, hy']
      abel
    | tmul b c' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorComponent_tmul, hθ, add_smul,
        smul_mul_smul_comm]

end

/-- The right tensor unitor is natural with respect to a linear map in its left factor. -/
@[simp]
theorem rid_rTensor_apply (f : M →ₗ[R] N) (t : M ⊗[R] R) :
    TensorProduct.rid R N (rTensor R f t) = f (TensorProduct.rid R M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m r => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The Casimir element of a trace

Let `φ : A →ₗ[k] k` be a trace on a `k`-algebra `A`, so `φ (a * b) = φ (b * a)`, and let `x` and
`y` be finite families dual to each other for the pairing `(a, b) ↦ φ (a * b)`, in the sense that
every element expands in either family with coefficients read off by pairing against the other:

```text
a = ∑ i, φ (a * y i) • x i,        a = ∑ i, φ (x i * a) • y i.
```

For a finite free symmetric Frobenius algebra, a basis and its dual basis give such families;
the expansion identities also allow redundant families. The **Casimir element** `∑ i, x i ⊗ y i`
of `A ⊗[k] A` then commutes with `A` in the bimodule sense:

```text
∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a).
```

This is what makes `1 ↦ ∑ i, x i ⊗ y i` a map of `A`-bimodules `A → A ⊗[k] A`, the coevaluation of
a symmetric Frobenius algebra; for a Frobenius coalgebra in Mathlib's sense
(`Coalgebra.IsFrobenius`) with counit `φ`, the element is the comultiplication of `1`.

The tensor identity itself needs only a `k`-module `A` with an associative multiplication.
No multiplicative identity, distributivity, or compatibility with scalar multiplication is needed.

-/

section Casimir

variable {k A : Type*} [CommSemiring k] [AddCommMonoid A] [Semigroup A] [Module k A]

/-- **The Casimir element of a trace commutes with multiplication.** If `φ` is a trace on `A`
and the finite families `x` and `y` are dual for `(a, b) ↦ φ (a * b)`, then
`∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a)` for every `a : A`. -/
theorem sum_mul_tmul_eq_sum_tmul_mul {ι : Type*} [Fintype ι] (φ : A →ₗ[k] k)
    (hφ : ∀ a b : A, φ (a * b) = φ (b * a)) {x y : ι → A}
    (hx : ∀ a : A, ∑ i, φ (a * y i) • x i = a) (hy : ∀ a : A, ∑ i, φ (x i * a) • y i = a)
    (a : A) :
    ∑ i, (a * x i) ⊗ₜ[k] y i = ∑ i, x i ⊗ₜ[k] (y i * a) := by
  -- Expand each `a * x i` in the family `x`; the coefficients then match those of the expansion
  -- of `y j * a` in the family `y`, by the trace property.
  have expand (i : ι) :
      (a * x i) ⊗ₜ[k] y i = ∑ j, x j ⊗ₜ[k] (φ (x i * (y j * a)) • y i) := by
    conv_lhs => rw [← hx (a * x i)]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul, mul_assoc, hφ, mul_assoc]
  simp_rw [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.tmul_sum, hy]

end Casimir

/-- If `c : M →ₗ[R] N` has a left inverse `l` and `c.lTensor κ = 0`, then `κ ⊗[R] M` is
trivial. -/
theorem subsingleton_tensor_of_lTensor_eq_zero {R M N κ : Type*} [CommSemiring R]
    [AddCommMonoid κ] [Module R κ] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (c : M →ₗ[R] N) (l : N →ₗ[R] M) (hl : l ∘ₗ c = LinearMap.id) (h : c.lTensor κ = 0) :
    Subsingleton (κ ⊗[R] M) := by
  have hinjective : Function.Injective (c.lTensor κ) := by
    intro x y hxy
    have h := congrArg (l.lTensor κ) hxy
    simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hl,
      LinearMap.lTensor_id, LinearMap.id_apply] using h
  constructor
  intro x y
  apply hinjective
  rw [h]
  rfl

end LinearMap

namespace TensorProduct

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- If a finite family `n` spans `N`, then every element of `M ⊗[R] N` is `∑ j, mⱼ ⊗ nⱼ` for some
family `m` of elements of `M`. -/
theorem exists_eq_sum_tmul_of_span_eq_top {κ : Type*} [Fintype κ] {n : κ → N}
    (hn : Submodule.span R (Set.range n) = ⊤) (x : M ⊗[R] N) :
    ∃ m : κ → M, x = ∑ j, m j ⊗ₜ[R] n j := by
  induction x with
  | tmul a y =>
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
      (hn ▸ Submodule.mem_top : y ∈ Submodule.span R (Set.range n))
    exact ⟨fun j ↦ c j • a, by simp [tmul_sum, smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact ⟨m + m', by simp [add_tmul, Finset.sum_add_distrib]⟩

/-- Splitting `F ⊗ F - id - (D ⊗ id + id ⊗ D)` into the terms in which one factor is the defect
`F - id - D` and the term `(F - id) ⊗ (F - id)` in which both factors move. -/
theorem map_sub_sub_add_eq {R : Type*} [CommSemiring R] {P : Type*} [AddCommGroup P] [Module R P]
    (F D : P →ₗ[R] P) (w : P ⊗[R] P) :
    map F F w - w - (LinearMap.rTensor _ D w + LinearMap.lTensor _ D w) =
      map (F - LinearMap.id - D) LinearMap.id w +
        map LinearMap.id (F - LinearMap.id - D) w +
        map (F - LinearMap.id) (F - LinearMap.id) w := by
  have hr : map (F - LinearMap.id) (LinearMap.id (M := P)) =
      map (F - LinearMap.id - D) LinearMap.id + map D LinearMap.id := by
    rw [← map_add_left]
    congr 1
    abel
  have hl : map (LinearMap.id (M := P)) (F - LinearMap.id) =
      map LinearMap.id (F - LinearMap.id - D) + map LinearMap.id D := by
    rw [← map_add_right]
    congr 1
    abel
  conv_lhs => rw [← add_sub_cancel LinearMap.id F]
  rw [map_add_left, map_add_right, map_add_right,
    map_id, hr, hl]
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.rTensor_def,
    LinearMap.lTensor_def]
  abel

variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- Exchanging the factors of both arguments of `tensorTensorTensorComm` exchanges the factors of
its value: `(n ⊗ m) ⊗ (q ⊗ p) ↦ (n ⊗ q) ⊗ (m ⊗ p)` is the exchange of
`(m ⊗ n) ⊗ (p ⊗ q) ↦ (m ⊗ p) ⊗ (n ⊗ q)`. -/
theorem tensorTensorTensorComm_comm_tmul_comm (x : M ⊗[R] N) (y : P ⊗[R] Q) :
    tensorTensorTensorComm R N M Q P (TensorProduct.comm R M N x ⊗ₜ TensorProduct.comm R P Q y) =
      TensorProduct.comm R _ _ (tensorTensorTensorComm R M N P Q (x ⊗ₜ y)) := by
  induction x using TensorProduct.inductionOn with
  | add x x' h h' => simp only [map_add, add_tmul, h, h']
  | tmul m n =>
    induction y using TensorProduct.inductionOn with
    | add y y' h h' => simp only [map_add, tmul_add, h, h']
    | tmul p q => simp

/-- If `M ⊗[R] N` is nontrivial then so is `N`: were `N` trivial, the tensor product would be
trivial too (`TensorProduct.uniqueRight`). -/
theorem nontrivial_right [Nontrivial (M ⊗[R] N)] : Nontrivial N :=
  not_subsingleton_iff_nontrivial.1 fun _ =>
    not_subsingleton (M ⊗[R] N) uniqueRight.instSubsingleton

end TensorProduct
