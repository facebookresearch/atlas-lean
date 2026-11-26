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

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Lp.LpEquiv
public import MathlibExt.Algebra.Star.CuntzFamily.Finite

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite Hilbert amplification from basis index splittings

Let `𝕜` be real or complex, `b` a Hilbert basis of `H` indexed by `ι`, and `e : Fin 2 × ι ≃ ι`.
The two basis embeddings `U_i b_j=b_(e(i,j))` satisfy `U_i* U_j=δ_ij I` and `U_0 U_0*+U_1
U_1*=I`.

Starting from `[I]`, split the last operator `V` into `V U_0,V U_1` repeatedly to obtain a
family `S_N` of any positive finite size `N`. It satisfies both finite Cuntz relations and
yields the isometric equivalence `H^N_(ℓ²) ≃ H`, `(x_i) ↦ Σ_i S_N(i)x_i`.

The Hilbert basis index may be arbitrary. Coefficient inclusions use the square-summable space
`lp 2`; the finite outer sum uses its two-norm. A zero space is permitted when the given index
data allow it.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProduct lp

namespace HilbertAmplification

universe u𝕜 uI uH

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {ι : Type uI} {H : Type uH}

/-- **Scalar inclusion at an embedded Hilbert coordinate.** Let `𝕜` be real or complex, `ι` an
index type with decidable equality and `f : ι ↪ ι`. For `j ∈ ι`, `coefficientFiber f j : 𝕜
→ₗᵢ[𝕜] ℓ²(ι,𝕜)` sends `z` to the singleton sequence with value `z` at `f(j)` and zero
elsewhere. -/
def coefficientFiber [DecidableEq ι] (f : ι ↪ ι) (j : ι) :
    𝕜 →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2 where
  __ := lp.lsingle (𝕜 := 𝕜) (E := fun _ : ι => 𝕜) 2 (f j)
  norm_map' z := lp.norm_single (E := fun _ : ι => 𝕜) (p := 2) (by norm_num) (f j) z

/-- **Orthogonality of injected scalar coordinates.** Let `𝕜` be real or complex, `ι` have
decidable equality and `f : ι ↪ ι`. The scalar singleton inclusions `z ↦ single_(f(j))(z)`
form an orthogonal family in `ℓ²(ι,𝕜)` as `j` varies. -/
theorem coefficientFiber_orthogonal [DecidableEq ι] (f : ι ↪ ι) :
    OrthogonalFamily 𝕜 (fun _ : ι => 𝕜) (coefficientFiber f) := by
  intro i j hij z w
  change inner 𝕜 (lp.single (E := fun _ : ι => 𝕜) 2 (f i) z)
    (lp.single (E := fun _ : ι => 𝕜) 2 (f j) w) = 0
  rw [lp.inner_single_left,
    lp.single_apply_ne (E := fun _ : ι => 𝕜) 2 (f j) w (f.injective.ne hij)]
  exact inner_zero_right _

/-- **Isometric embedding of square-summable coordinates.** Let `𝕜` be real or complex, `ι`
have decidable equality and `f : ι ↪ ι`. `coefficientEmbedding f : ℓ²(ι,𝕜) →ₗᵢ[𝕜] ℓ²(ι,𝕜)`
moves the `j`th coefficient to `f(j)` and sets coordinates outside the image to zero. -/
def coefficientEmbedding [DecidableEq ι] (f : ι ↪ ι) :
    lp (fun _ : ι => 𝕜) 2 →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2 :=
  (coefficientFiber_orthogonal f).linearIsometry

/-- **Injected singleton sequence under the coordinate embedding.** Let `𝕜` be real or
complex, `ι` have decidable equality and `f : ι ↪ ι`. For `j ∈ ι`, `z : 𝕜`,
`coefficientEmbedding f (single_j z)=single_(f(j)) z`. -/
@[simp]
theorem coefficientEmbedding_single [DecidableEq ι] (f : ι ↪ ι) (j : ι) (z : 𝕜) :
    coefficientEmbedding f (lp.single (E := fun _ : ι => 𝕜) 2 j z) =
      lp.single (E := fun _ : ι => 𝕜) 2 (f j) z :=
  (coefficientFiber_orthogonal (𝕜 := 𝕜) f).linearIsometry_apply_single (i := j) z

variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Hilbert basis vector represented by a scalar singleton.** Let `𝕜` be real or complex, `b
: HilbertBasis ι 𝕜 H` and assume decidable equality on `ι`. For `j ∈ ι`, `z : 𝕜`,
`b.repr.symm(single_j z)=z • b_j`. -/
private theorem repr_symm_single_smul [DecidableEq ι] (b : HilbertBasis ι 𝕜 H)
    (j : ι) (z : 𝕜) :
    b.repr.symm (lp.single (E := fun _ : ι => 𝕜) 2 j z) = z • b j := by
  have h : lp.single (E := fun _ : ι => 𝕜) 2 j z =
      z • lp.single (E := fun _ : ι => 𝕜) 2 j (1 : 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : ι => 𝕜) 2 j z (1 : 𝕜)
  rw [h, map_smul, b.repr_symm_single]

/-- **Basis-coordinate isometry from an index injection.** Let `𝕜` be real or complex, `b :
HilbertBasis ι 𝕜 H` and `f : ι ↪ ι`. `coordinateEmbedding b f : H →ₗᵢ[𝕜] H` is the basis
transport of the singleton coordinate embedding, characterized by `b_j ↦ b_(f(j))`. -/
def coordinateEmbedding (b : HilbertBasis ι 𝕜 H) (f : ι ↪ ι) :
    H →ₗᵢ[𝕜] H := by
  classical
  exact b.repr.symm.toLinearIsometry.comp
    ((coefficientEmbedding f).comp b.repr.toLinearIsometry)

/-- **Basis action of an injected Hilbert coordinate.** Let `𝕜` be real or complex, `b :
HilbertBasis ι 𝕜 H` and `f : ι ↪ ι`. For `j ∈ ι`, `coordinateEmbedding b f
(b_j)=b_(f(j))`. -/
@[simp]
theorem coordinateEmbedding_basis (b : HilbertBasis ι 𝕜 H) (f : ι ↪ ι) (j : ι) :
    coordinateEmbedding b f (b j) = b (f j) := by
  classical
  change b.repr.symm (coefficientEmbedding f (b.repr (b j))) = b (f j)
  rw [b.repr_self, coefficientEmbedding_single, b.repr_symm_single]

/-- **Scalar basis coefficient under coordinate injection.** Let `𝕜` be real or complex, `b :
HilbertBasis ι 𝕜 H`, `f : ι ↪ ι`, and assume decidable equality on `ι`. For `j ∈ ι`, `z :
𝕜`, `coordinateEmbedding b f (b.repr.symm(single_j z))=b.repr.symm(single_(f(j)) z)`. -/
theorem coordinateEmbedding_repr_symm_single [DecidableEq ι]
    (b : HilbertBasis ι 𝕜 H) (f : ι ↪ ι) (j : ι) (z : 𝕜) :
    coordinateEmbedding b f (b.repr.symm (lp.single (E := fun _ : ι => 𝕜) 2 j z)) =
      b.repr.symm (lp.single (E := fun _ : ι => 𝕜) 2 (f j) z) := by
  rw [repr_symm_single_smul, map_smul, coordinateEmbedding_basis,
    ← repr_symm_single_smul b (f j) z]

/-- **Coordinate embedding for the identity Hilbert representation.** Let `𝕜` be real or
complex, `ι` have decidable equality and `f : ι ↪ ι`. On `H=ℓ²(ι,𝕜)` with the Hilbert
basis given by the identity representation, `coordinateEmbedding b f=coefficientEmbedding
f`. -/
theorem coordinateEmbedding_ofRepr_refl [DecidableEq ι] (f : ι ↪ ι) :
    coordinateEmbedding (HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 _)) f =
      coefficientEmbedding f := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply lp.ext_continuousLinearMap (𝕜 := 𝕜) (E := fun _ : ι => 𝕜) (p := 2) (by norm_num)
  intro j
  apply ContinuousLinearMap.ext
  intro z
  exact (coordinateEmbedding_repr_symm_single
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 _)) f j z).trans
    (coefficientEmbedding_single f j z).symm

variable [CompleteSpace H]

/-- **Adjoint coordinate extraction in a Hilbert basis.** Let `𝕜` be real or complex, `b :
HilbertBasis ι 𝕜 H` and `f : ι ↪ ι`. For `x ∈ H`, the `j`th basis coefficient of
`(coordinateEmbedding b f)*x` equals the `f(j)`th basis coefficient of `x`. -/
theorem coordinateEmbedding_adjoint_repr (b : HilbertBasis ι 𝕜 H) (f : ι ↪ ι)
    (x : H) (j : ι) :
    b.repr ((coordinateEmbedding b f).toContinuousLinearMap.adjoint x) j =
      b.repr x (f j) := by
  rw [b.repr_apply_apply, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, coordinateEmbedding_basis,
    ← b.repr_apply_apply]

/-- **Adjoint of a scalar coordinate injection.** Let `𝕜` be real or complex, `ι` have
decidable equality and `f : ι ↪ ι`. For `x ∈ ℓ²(ι,𝕜)`, `(coefficientEmbedding f)* x` has
`j`th coefficient `x_(f(j))`. -/
theorem coefficientEmbedding_adjoint_apply [DecidableEq ι] (f : ι ↪ ι)
    (x : lp (fun _ : ι => 𝕜) 2) (j : ι) :
    ((coefficientEmbedding f).toContinuousLinearMap.adjoint x) j = x (f j) := by
  have h := coordinateEmbedding_adjoint_repr
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 _)) f x j
  rw [coordinateEmbedding_ofRepr_refl] at h
  exact h

/-- **Adjoint returns an injected singleton coefficient.** Let `𝕜` be real or complex, `ι`
have decidable equality and `f : ι ↪ ι`. For `j ∈ ι`, `z : 𝕜`, `(coefficientEmbedding
f)*(single_(f(j)) z)=single_j z`. -/
@[simp]
theorem coefficientEmbedding_adjoint_single_image [DecidableEq ι] (f : ι ↪ ι)
    (j : ι) (z : 𝕜) :
    (coefficientEmbedding f).toContinuousLinearMap.adjoint
        (lp.single (E := fun _ : ι => 𝕜) 2 (f j) z) =
      lp.single (E := fun _ : ι => 𝕜) 2 j z := by
  ext k
  rw [coefficientEmbedding_adjoint_apply]
  simp only [lp.single_apply, Pi.single_apply, f.injective.eq_iff]

/-- **Adjoint kills a singleton outside the injected range.** Let `𝕜` be real or complex, `ι`
have decidable equality and `f : ι ↪ ι`. If `k∈ι` is outside `range f`, then for every `z
: 𝕜`, `(coefficientEmbedding f)*(single_k z)=0`. -/
theorem coefficientEmbedding_adjoint_single_off [DecidableEq ι] (f : ι ↪ ι)
    (k : ι) (z : 𝕜) (hk : ∀ j, f j ≠ k) :
    (coefficientEmbedding f).toContinuousLinearMap.adjoint
        (lp.single (E := fun _ : ι => 𝕜) 2 k z) = 0 := by
  ext j
  rw [coefficientEmbedding_adjoint_apply]
  simpa only [lp.coeFn_zero, Pi.zero_apply] using
    lp.single_apply_ne (E := fun _ : ι => 𝕜) 2 k z (hk j)

omit [CompleteSpace H] in
/-- **Binary basis embedding from an index bijection.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin
2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. `binaryEmbedding
b e i : H →ₗᵢ[𝕜] H` is `U_i`, the embedding corresponding to the injection `j ↦ e(i,j)`. -/
def binaryEmbedding (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι)
    (i : Fin 2) : H →ₗᵢ[𝕜] H :=
  coordinateEmbedding b
    ⟨fun j => e (i, j), fun _j _k h => congrArg Prod.snd (e.injective h)⟩

omit [CompleteSpace H] in
/-- **Basis value of a binary Hilbert embedding.** Let `𝕜` be real or complex, `H` a normed
inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin 2 × ι)
≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. for `i ∈ Fin 2` and `j
∈ ι`, `binaryEmbedding b e i (b_j)=b_(e(i,j))`. -/
@[simp]
theorem binaryEmbedding_basis (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (i : Fin 2) (j : ι) :
    binaryEmbedding b e i (b j) = b (e (i, j)) :=
  coordinateEmbedding_basis b _ j

omit [CompleteSpace H] in
private theorem basis_inner_ext (b : HilbertBasis ι 𝕜 H) {x y : H}
    (h : ∀ j, inner 𝕜 (b j) x = inner 𝕜 (b j) y) : x = y := by
  apply b.repr.injective
  ext j
  simpa only [b.repr_apply_apply] using h j

omit [CompleteSpace H] in
private theorem basis_map_ext (b : HilbertBasis ι 𝕜 H) {A B : H →L[𝕜] H}
    (h : ∀ j, A (b j) = B (b j)) : A = B := by
  have hd : Dense (Submodule.span 𝕜 (Set.range b) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  apply ContinuousLinearMap.ext_on hd
  rintro x ⟨j, rfl⟩
  exact h j

/-- **Binary adjoint selects its coordinate block.** Let `𝕜` be real or complex, `H` a normed
inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin 2 × ι)
≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. for `i,j ∈ Fin 2` and
`m ∈ ι`, `U_i* b_(e(j,m))` equals `b_m` when `i=j` and zero otherwise. -/
theorem binaryEmbedding_adjoint_basis (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (i j : Fin 2) (m : ι) :
    (binaryEmbedding b e i).toContinuousLinearMap.adjoint (b (e (j, m))) =
      if i = j then b m else 0 := by
  classical
  apply basis_inner_ext b
  intro k
  rw [ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, binaryEmbedding_basis]
  rw [orthonormal_iff_ite.mp b.orthonormal]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, orthonormal_iff_ite.mp b.orthonormal]
    simp only [e.injective.eq_iff, Prod.mk.injEq, true_and]
  · rw [ite_eq_right hij, inner_zero_right]
    simp only [e.injective.eq_iff, Prod.mk.injEq, hij, false_and, ite_false]

omit [CompleteSpace H] in
/-- **Binary Cuntz operators from Hilbert coordinates.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin
2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. `binaryFamily b
e : Fin 2 → B(H)` is the bounded operator family `i ↦ U_i`. -/
def binaryFamily (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι) :
    Fin 2 → (H →L[𝕜] H) :=
  fun i => (binaryEmbedding b e i).toContinuousLinearMap

/-- **Binary Cuntz Gram relations.** Let `𝕜` be real or complex, `H` a normed inner-product
`𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin 2 × ι) ≃ ι` an index
bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. `U_i* U_j=I_H` for `i=j` and zero for
`i≠j`. -/
theorem binaryFamily_orthogonal (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (i j : Fin 2) :
    star (binaryFamily b e i) * binaryFamily b e j =
      if i = j then 1 else 0 := by
  classical
  apply basis_map_ext b
  intro m
  change (binaryEmbedding b e i).toContinuousLinearMap.adjoint
      (binaryEmbedding b e j (b m)) =
    (if i = j then (1 : H →L[𝕜] H) else 0) (b m)
  rw [binaryEmbedding_basis, binaryEmbedding_adjoint_basis]
  by_cases hij : i = j <;> simp [hij]

/-- **Binary coordinate ranges partition the Hilbert space.** Let `𝕜` be real or complex, `H`
a normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e :
(Fin 2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. `U_0
U_0*+U_1 U_1*=I_H`. -/
theorem binaryFamily_partition (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) :
    binaryFamily b e 0 * star (binaryFamily b e 0) +
      binaryFamily b e 1 * star (binaryFamily b e 1) = 1 := by
  apply basis_map_ext b
  intro m
  obtain ⟨⟨j, k⟩, rfl⟩ := e.surjective m
  fin_cases j <;>
    simp [binaryFamily, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      binaryEmbedding_adjoint_basis, binaryEmbedding_basis]

/-- **Positive finite Cuntz family by successive last-leaf splitting.** Let `𝕜` be real or
complex, `H` a normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`,
and `e : (Fin 2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`.
For `N : ℕ+`, form `S_N` from the singleton family `[I]` by repeatedly replacing its last
operator `V` with `V U_0,V U_1` until the family has `N` operators. `finiteFamily b e N :
Fin N → B(H)` is this family `S_N`, with the unchanged earlier operators followed by `V
U_0,V U_1` at each split. -/
def finiteFamily (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι)
    (N : ℕ+) : Fin N → (H →L[𝕜] H) :=
  CuntzFamily.ofBinaryPositive (binaryFamily b e) N

/-- **Both finite Cuntz relations for coordinate amplification.** Let `𝕜` be real or complex,
`H` a normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e :
(Fin 2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. For `N :
ℕ+`, form `S_N` from the singleton family `[I]` by repeatedly replacing its last operator
`V` with `V U_0,V U_1` until the family has `N` operators. `S_N(i)* S_N(j)=δ_ij I_H` for
all `i,j ∈ Fin N`, and `Σ_i S_N(i)S_N(i)*=I_H`. -/
theorem finiteFamily_relations (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    (∀ i j : Fin N,
      star (finiteFamily b e N i) * finiteFamily b e N j =
        if i = j then 1 else 0) ∧
    (∑ i : Fin N, finiteFamily b e N i * star (finiteFamily b e N i)) = 1 :=
  CuntzFamily.ofBinaryPositive_relations (binaryFamily b e)
    (binaryFamily_orthogonal b e) (binaryFamily_partition b e) N

/-- **Isometric inclusion from a finite Cuntz operator.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin
2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. For `N : ℕ+`,
form `S_N` from the singleton family `[I]` by repeatedly replacing its last operator `V`
with `V U_0,V U_1` until the family has `N` operators. for `i ∈ Fin N`, `finiteEmbedding b
e N i : H →ₗᵢ[𝕜] H` is the linear isometry with underlying bounded operator `S_N(i)`. -/
def finiteEmbedding (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι)
    (N : ℕ+) (i : Fin N) : H →ₗᵢ[𝕜] H where
  toLinearMap := (finiteFamily b e N i).toLinearMap
  norm_map' := by
    have h : star (finiteFamily b e N i) * finiteFamily b e N i = 1 :=
      ((finiteFamily_relations b e N).1 i i).trans (ite_eq_left rfl)
    rw [ContinuousLinearMap.star_eq_adjoint] at h
    exact (finiteFamily b e N i).norm_map_iff_adjoint_comp_self.mpr h

/-- **Vector value of a finite Hilbert embedding.** Let `𝕜` be real or complex, `H` a normed
inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin 2 × ι)
≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. For `N : ℕ+`, form
`S_N` from the singleton family `[I]` by repeatedly replacing its last operator `V` with
`V U_0,V U_1` until the family has `N` operators. for `i ∈ Fin N` and `x ∈ H`,
`finiteEmbedding b e N i x=S_N(i)x`. -/
theorem finiteEmbedding_apply (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) (i : Fin N) (x : H) :
    finiteEmbedding b e N i x = finiteFamily b e N i x :=
  rfl

/-- **Orthogonal total Hilbert sum from the finite family.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin
2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. For `N : ℕ+`,
form `S_N` from the singleton family `[I]` by repeatedly replacing its last operator `V`
with `V U_0,V U_1` until the family has `N` operators. the isometries `finiteEmbedding b e
N i` have pairwise orthogonal ranges whose Hilbert sum is all of `H`. -/
theorem finiteFamily_isHilbertSum (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    IsHilbertSum 𝕜 (fun _ : Fin N => H) (finiteEmbedding b e N) := by
  classical
  refine IsHilbertSum.mk ?_ ?_
  · intro i j hij x y
    have hzero : star (finiteFamily b e N i) * finiteFamily b e N j = 0 := by
      simpa only [ite_eq_right hij] using (finiteFamily_relations b e N).1 i j
    change inner 𝕜 (finiteFamily b e N i x) (finiteFamily b e N j y) = 0
    calc
      _ = inner 𝕜 x
          ((finiteFamily b e N i).adjoint (finiteFamily b e N j y)) :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = 0 := by
        have h := congrArg (fun T : H →L[𝕜] H => T y) hzero
        change (finiteFamily b e N i).adjoint (finiteFamily b e N j y) = 0 at h
        rw [h, inner_zero_right]
  · intro x _
    apply (Submodule.le_topologicalClosure _)
    have h := congrArg (fun T : H →L[𝕜] H => T x) (finiteFamily_relations b e N).2
    have hsum : (∑ i : Fin N,
        finiteFamily b e N i (star (finiteFamily b e N i) x)) = x := by
      simpa only [_root_.sum_apply, mul_apply_eq_comp, one_apply_eq_self] using h
    rw [← hsum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.mem_iSup_of_mem i
      ⟨star (finiteFamily b e N i) x, rfl⟩

/-- **Finite two-norm amplification of a Hilbert space.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin
2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. For `N : ℕ+`,
form `S_N` from the singleton family `[I]` by repeatedly replacing its last operator `V`
with `V U_0,V U_1` until the family has `N` operators. `finiteAmplification b e N : PiLp 2
(fun _ : Fin N => H) ≃ₗᵢ[𝕜] H` sends `(x_i)` to `Σ_i S_N(i)x_i`. -/
def finiteAmplification (b : HilbertBasis ι 𝕜 H) (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    PiLp 2 (fun _ : Fin N => H) ≃ₗᵢ[𝕜] H :=
  (lpPiLpₗᵢ (fun _ : Fin N => H) 𝕜 (p := 2)).symm.trans
    (finiteFamily_isHilbertSum b e N).linearIsometryEquiv.symm

/-- **Ordered finite-sum value of Hilbert amplification.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin
2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. For `N : ℕ+`,
form `S_N` from the singleton family `[I]` by repeatedly replacing its last operator `V`
with `V U_0,V U_1` until the family has `N` operators. for `x ∈ H^N` with its two-norm,
`finiteAmplification b e N x=Σ_i∈Fin N S_N(i)(x_i)`. -/
theorem finiteAmplification_apply (b : HilbertBasis ι 𝕜 H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) (x : PiLp 2 (fun _ : Fin N => H)) :
    finiteAmplification b e N x = ∑ i : Fin N, finiteFamily b e N i (x i) := by
  change (finiteFamily_isHilbertSum b e N).linearIsometryEquiv.symm
    ((lpPiLpₗᵢ (fun _ : Fin N => H) 𝕜 (p := 2)).symm x) = _
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply, tsum_fintype]
  rfl

end HilbertAmplification
