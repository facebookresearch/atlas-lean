/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProductSurjective
public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverLocalDegree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Localization

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open TensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

/-!
# The finite-place completion tensor product

This file proves the number-field specialization of part (5) of ATLAS
`NumberTheoryI` target N236, Theorem 11.23, which supplies the finite-place
tensor-product ingredient used later in target N265, Theorem 13.5. The source
statement identifies
`L ⊗[K] K_p` with the product of the completions `L_q` over all `q ∣ p`, with
`l ⊗ x` sent to the tuple `(l * x)_q`. At atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, see the
[Theorem 11.23 target, lines 1668--1684](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1668-L1684)
and the primary Lean source
[`theorem_11_23_part5_tensor_product_decomp`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2954-L3025).
Its isomorphism component delegates to the admission-backed
[`theorem_11_23_part5_iso_from_weak_approx`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2936-L2951).

We specialize the source's Dedekind domains `A` and `B` to `𝓞 K` and `𝓞 L`.
The source prime `p` is `v.asIdeal`, and `v.placesOver L` is the family of source
primes `q ∣ p`. Our tensor factors are commuted: the source `L ⊗[K] K_v` is
represented as `K_v ⊗[K] L`. Accordingly, `completionTensorProductMap` sends
`x ⊗ₜ y` to the function whose `w`-coordinate is the image of `x` in `L_w`
times the image of `y` in `L_w`; this is exactly the source map after swapping
the factors.

The proof replaces the source's admission-backed kernel/isomorphism route. Part (4)
gives `[L_w : K_v] = e_w f_w`; the global ramification--inertia sum gives
`∑_{w∣v} e_w f_w = [L : K]`. Base change gives
`dim_{K_v}(K_v ⊗[K] L) = [L : K]`, while dimension of the finite product is the
sum of its local dimensions. The already-proved surjectivity of the canonical
map and this equality of finite dimensions imply injectivity and hence the
algebra equivalence. The last theorem records the source's coordinate formula.

The right-oriented equivalence below also matches ATLAS `NumberTheoryI` target
N265, Theorem 13.5, whose exact finite-place implementation is
[`theorem_13_5_finite_place_Kv` in
`v1/Atlas/NumberTheoryI/code/GlobalFields.lean`, lines 1152--1166](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1152-L1166).
Its hypotheses are a finite
separable extension of global fields and a place `v`; here we specialize to
number fields, where `v : HeightOneSpectrum (𝓞 K)` is a finite place and
`v.placesOver L` is the family `w ∣ v`. The source's existential `K_v`-algebra
equivalence is made explicit, and its required coordinate law
`α ⊗ 1 ↦ (algebraMap L L_w α)_w` is
`completionTensorProductRightAlgEquiv_tmul_one`. The more general pure-tensor
formula records the same map on `y ⊗ x`. Infinite places and the general
function-field case remain outside this file's scope.
-/

/-- **Local degrees sum to the global degree.** Let $L/K$ be an extension of number fields, $v$ a
finite place of $K$ and $K_v$ the completion of $K$ at $v$; for each finite place $w$ of $L$ lying
over $v$, let $L_w$ be the completion of $L$ at $w$, a $K_v$-algebra via the canonical map
$K_v \to L_w$. Then $\sum_{w \mid v} [L_w : K_v] = [L : K]$.

Source: ATLAS N236, Theorem 11.23, parts (4) and (5) combined; used in N265. -/
theorem sum_finrank_adicCompletion_placesOver [Fintype (v.placesOver L)] :
    ∑ w : v.placesOver L,
      Module.finrank (v.adicCompletion K) (w.val.adicCompletion L) =
      Module.finrank K L := by
  classical
  let _ := Fintype.ofFinite (v.asIdeal.primesOver (𝓞 L))
  have hrewrite : ∀ w : v.placesOver L,
      Module.finrank (v.adicCompletion K) (w.val.adicCompletion L) =
        w.val.asIdeal.ramificationIdx (𝓞 K) *
          w.val.asIdeal.inertiaDeg (𝓞 K) := by
    intro w
    let _ : w.val.asIdeal.LiesOver v.asIdeal := w.property
    exact finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg v w.val
  simp_rw [hrewrite]
  have hsum := Equiv.sum_comp (v.placesOverEquivPrimesOver L)
    (fun Q : v.asIdeal.primesOver (𝓞 L) =>
      Q.val.ramificationIdx (𝓞 K) * Q.val.inertiaDeg (𝓞 K))
  have happly : (∑ w : v.placesOver L,
      ((fun Q : v.asIdeal.primesOver (𝓞 L) =>
        Q.val.ramificationIdx (𝓞 K) * Q.val.inertiaDeg (𝓞 K))
        ((v.placesOverEquivPrimesOver L) w))) =
      ∑ Q : v.asIdeal.primesOver (𝓞 L),
        Q.val.ramificationIdx (𝓞 K) * Q.val.inertiaDeg (𝓞 K) := hsum
  have hpointwise : (∑ w : v.placesOver L,
      w.val.asIdeal.ramificationIdx (𝓞 K) *
        w.val.asIdeal.inertiaDeg (𝓞 K)) =
      (∑ w : v.placesOver L,
      ((fun Q : v.asIdeal.primesOver (𝓞 L) =>
        Q.val.ramificationIdx (𝓞 K) * Q.val.inertiaDeg (𝓞 K))
        ((v.placesOverEquivPrimesOver L) w))) := by rfl
  rw [hpointwise, happly,
    Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L),
    IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]

/-- **Dimension count for the base change to a finite completion.** Let $L/K$ be an extension of
number fields, $v$ a finite place of $K$ and $K_v$ the completion of $K$ at $v$; for each finite
place $w$ of $L$ lying over $v$, let $L_w$ be the completion of $L$ at $w$, a $K_v$-algebra via
the canonical map $K_v \to L_w$. Then $K_v \otimes_K L$ and $\prod_{w \mid v} L_w$ have the same
dimension as $K_v$-vector spaces. -/
theorem finrank_completionTensorProduct_eq_pi :
    Module.finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) =
      Module.finrank (v.adicCompletion K)
        ((w : v.placesOver L) → w.val.adicCompletion L) := by
  classical
  let _ := Fintype.ofFinite (v.placesOver L)
  rw [Module.finrank_baseChange, Module.finrank_pi_fintype,
    sum_finrank_adicCompletion_placesOver v]

/-- **The canonical map to the product of completions is injective.** Let $L/K$ be an extension of
number fields, $v$ a finite place of $K$ and $K_v$ the completion of $K$ at $v$; for each finite
place $w$ of $L$ lying over $v$, let $L_w$ be the completion of $L$ at $w$, a $K_v$-algebra via
the canonical map $K_v \to L_w$. The $K_v$-algebra map $K_v \otimes_K L \to \prod_{w \mid v} L_w$
sending $x \otimes y$ to $(x y)_w$, where $x \in K_v$ and $y \in L$ are mapped into each $L_w$,
is injective. -/
theorem completionTensorProductMap_injective :
    Function.Injective (completionTensorProductMap (K := K) (L := L) v) := by
  have hfin := finrank_completionTensorProduct_eq_pi (K := K) (L := L) v
  have hsurj := completionTensorProductMap_surjective (K := K) (L := L) v
  have hsurjLin : Function.Surjective
      ((completionTensorProductMap (K := K) (L := L) v).toLinearMap) := hsurj
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr
    hsurjLin

/-- **The canonical map to the product of completions is bijective.** Let $L/K$ be an extension of
number fields, $v$ a finite place of $K$ and $K_v$ the completion of $K$ at $v$; for each finite
place $w$ of $L$ lying over $v$, let $L_w$ be the completion of $L$ at $w$, a $K_v$-algebra via
the canonical map $K_v \to L_w$. The $K_v$-algebra map $K_v \otimes_K L \to \prod_{w \mid v} L_w$
sending $x \otimes y$ to $(x y)_w$, where $x \in K_v$ and $y \in L$ are mapped into each $L_w$,
is bijective. -/
theorem completionTensorProductMap_bijective :
    Function.Bijective (completionTensorProductMap (K := K) (L := L) v) :=
  ⟨completionTensorProductMap_injective v,
    completionTensorProductMap_surjective v⟩

/-- **Base change to a finite completion as a product of completions.** Let $L/K$ be an extension
of number fields, $v$ a finite place of $K$ and $K_v$ the completion of $K$ at $v$; for each finite
place $w$ of $L$ lying over $v$, let $L_w$ be the completion of $L$ at $w$, a $K_v$-algebra via the
canonical map $K_v \to L_w$. This is the isomorphism of $K_v$-algebras
$K_v \otimes_K L \cong \prod_{w \mid v} L_w$ sending $x \otimes y$ to $(x y)_w$, where $x \in K_v$
and $y \in L$ are mapped into each $L_w$.

Source: ATLAS N236, Theorem 11.23(5), with the tensor factors swapped; used later in N265. -/
noncomputable def completionTensorProductAlgEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ((w : v.placesOver L) → w.val.adicCompletion L) :=
  AlgEquiv.ofBijective (completionTensorProductMap (K := K) (L := L) v)
    (completionTensorProductMap_bijective (K := K) (L := L) v)

@[simp]
theorem completionTensorProductAlgEquiv_tmul (x : v.adicCompletion K) (y : L)
    (w : v.placesOver L) :
    completionTensorProductAlgEquiv (K := K) (L := L) v (x ⊗ₜ[K] y) w =
      Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
        (w.val.adicCompletion L) x * Algebra.algHom K L _ y := by
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Tensor product decomposition at a finite place.** Let $L/K$ be an extension of number fields,
$v$ a finite place of $K$ and $K_v$ the completion of $K$ at $v$; for each finite place $w$ of $L$
lying over $v$, let $L_w$ be the completion of $L$ at $w$, a $K_v$-algebra via the canonical map
$K_v \to L_w$, and make $L \otimes_K K_v$ a $K_v$-algebra through its second factor. This is the
isomorphism of $K_v$-algebras $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ sending $y \otimes x$
to $(y x)_w$, where $y \in L$ and $x \in K_v$ are mapped into each $L_w$.

Source: ATLAS N265, Theorem 13.5, the finite-place $K_v$-algebra form for number fields
(`theorem_13_5_finite_place_Kv` in the primary Lean source). -/
noncomputable def completionTensorProductRightAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K]
      ((w : v.placesOver L) → w.val.adicCompletion L) :=
  (Algebra.TensorProduct.commRight K (v.adicCompletion K) L).symm.trans
    (completionTensorProductAlgEquiv (K := K) (L := L) v)

@[simp]
theorem completionTensorProductRightAlgEquiv_tmul (y : L)
    (x : v.adicCompletion K) (w : v.placesOver L) :
    completionTensorProductRightAlgEquiv (K := K) (L := L) v (y ⊗ₜ[K] x) w =
      Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
        (w.val.adicCompletion L) x * Algebra.algHom K L _ y := by
  simp [completionTensorProductRightAlgEquiv,
    completionTensorProductAlgEquiv_tmul]

/-- **Coordinate law for the tensor product decomposition.** Let $L/K$ be an extension of number
fields, $v$ a finite place of $K$ and $K_v$ the completion of $K$ at $v$; for each finite place $w$
of $L$ lying over $v$, let $L_w$ be the completion of $L$ at $w$, a $K_v$-algebra via the canonical
map $K_v \to L_w$, and make $L \otimes_K K_v$ a $K_v$-algebra through its second factor. Consider
the isomorphism of $K_v$-algebras $L \otimes_K K_v \cong \prod_{w \mid v} L_w$ sending $a \otimes b$
to $(a b)_w$, where $a \in L$ and $b \in K_v$ are mapped into each $L_w$. For every $y \in L$ and
every finite place $w$ of $L$ lying over $v$, the $w$-coordinate of the image of $y \otimes 1$ is
the image of $y$ in $L_w$.

Source: ATLAS N265, Theorem 13.5, the coordinate law for pure tensors. -/
@[simp]
theorem completionTensorProductRightAlgEquiv_tmul_one (y : L)
    (w : v.placesOver L) :
    completionTensorProductRightAlgEquiv (K := K) (L := L) v
      (y ⊗ₜ[K] (1 : v.adicCompletion K)) w =
      algebraMap L (w.val.adicCompletion L) y := by
  simp only [completionTensorProductRightAlgEquiv_tmul, map_one, one_mul]
  rfl

/-- **Tensor product decomposition at a finite place over the base field.** Let $L/K$ be an
extension of number fields, $v$ a finite place of $K$ and $K_v$ the completion of $K$ at $v$; for
each finite place $w$ of $L$ lying over $v$, let $L_w$ be the completion of $L$ at $w$. There
exists an isomorphism of $K$-algebras $L \otimes_K K_v \cong \prod_{w \mid v} L_w$.

It is obtained by restricting scalars from $K_v$ to $K$ in the isomorphism of $K_v$-algebras
$L \otimes_K K_v \cong \prod_{w \mid v} L_w$ sending $y \otimes x$ to $(y x)_w$, where $y \in L$
and $x \in K_v$ are mapped into each $L_w$, $L_w$ is a $K_v$-algebra via the canonical map
$K_v \to L_w$, and $L \otimes_K K_v$ is a $K_v$-algebra through its second factor. -/
theorem completionTensorProductRightAlgEquiv_K :
    Nonempty (L ⊗[K] v.adicCompletion K ≃ₐ[K]
      ((w : v.placesOver L) → w.val.adicCompletion L)) :=
  ⟨(completionTensorProductRightAlgEquiv (K := K) (L := L) v).restrictScalars K⟩

end HeightOneSpectrum

end IsDedekindDomain
