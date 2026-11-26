/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.IdempotentImageSplits
public import MathlibExt.Algebra.Homology.LocallyFiniteSplitComplex
public import MathlibExt.Algebra.Homology.LocallyFiniteSplitHomology

/-!
# Locally finite decompositions by chain-idempotent images

Let C be an abelian category, K a complex of arbitrary shape c on ι,
and e_j : K → K, j ∈ ℕ, an orthogonal family of idempotents:
e_k ∘ e_j = e_j for j = k and zero for j ≠ k.
Write I_j = Im(e_j), with image inclusion i_j and factor p_j.
Then p_j ∘ i_j = id_(I_j), while p_k ∘ i_j = 0 for j ≠ k.

Suppose N : ι → ℕ bounds the degreewise support:
(e_j)_n = 0 for j > N(n), and ∑_(j=0)^(N(n)) (e_j)_n = id_(K_n).
If C has countable coproducts, the image inclusions give
⨁_j I_j ≅ K as complexes. In degree n the inverse is the finite sum
∑_(j=0)^(N(n)) ι_(j,n) ∘ (p_j)_n.

The induced homology maps similarly give
⨁_j H_n(I_j) ≅ H_n(K), with inverse
∑_(j=0)^(N(n)) ι_j ∘ H_n(p_j).
Only degreewise finite support is used; the object, morphism and index
universes of C and ι are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasColimitsOfShape (Discrete ℕ) C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (e : ℕ → (K ⟶ K))
  (he : ∀ i j : ℕ, e i ≫ e j = if i = j then e i else 0)
  (N : ι → ℕ)
  (hsupport : ∀ n : ι, ∀ j : ℕ, N n < j → (e j).f n = 0)
  (hsum : ∀ n : ι, (∑ j : Fin (N n + 1), (e j.val).f n) = 𝟙 (K.X n))

include he in
omit [HasColimitsOfShape (Discrete ℕ) C] in
/-- In an abelian category C, let e_j be an orthogonal
idempotent family on a complex K of any shape. For every j, the
image inclusion i_j : Im(e_j) → K and factor p_j : K → Im(e_j)
satisfy p_j ∘ i_j = id_(Im(e_j)).
This identity does not require coproducts in C. -/
theorem idempotentImage_split (j : ℕ) :
    image.ι (e j) ≫ factorThruImage (e j) = 𝟙 (image (e j)) :=
  image_ι_factorThruImage_of_idempotent (e j) ((he j j).trans (ite_eq_left (rfl : j = j)))

include he in
omit [HasColimitsOfShape (Discrete ℕ) C] in
/-- In an abelian category C, let e_j be an orthogonal
idempotent family on a complex K of any shape. For j ≠ k, the map
Im(e_j) → K → Im(e_k), given by image inclusion and factor,
is zero. No coproduct assumption is needed. -/
theorem idempotentImage_cross (j k : ℕ) (hjk : j ≠ k) :
    image.ι (e j) ≫ factorThruImage (e k) = 0 :=
  image_ι_factorThruImage_of_comp_zero (e j) (e k) ((he j k).trans (ite_eq_right hjk))

include hsupport in
omit [HasColimitsOfShape (Discrete ℕ) C] in
/-- Let K be a complex of any shape in an abelian category C,
let e_j : K → K be chain endomorphisms and N : ι → ℕ a bound.
If (e_j)_n = 0 for j > N(n), then the degree-n component of
K → Im(e_j) is zero for those j.
This conclusion uses the support condition, without an
orthogonality or coproduct assumption. -/
theorem idempotentImage_factor_support (n : ι) (j : ℕ) (hj : N n < j) :
    (factorThruImage (e j)).f n = 0 := by
  apply (cancel_mono ((image.ι (e j)).f n)).mp
  have h := congrArg (fun f => f.f n) (image.fac (e j))
  simpa only [HomologicalComplex.comp_f, hsupport n j hj, zero_comp] using h

include hsum in
omit [HasColimitsOfShape (Discrete ℕ) C] in
/-- For a complex K in an abelian category C and chain
endomorphisms e_j, suppose
∑_(j=0)^(N(n)) (e_j)_n = id_(K_n) in every degree n.
Writing i_j,p_j for the image inclusion and factor gives
∑_(j=0)^(N(n)) (i_j)_n ∘ (p_j)_n = id_(K_n).
No orthogonality premise is required for this factorization equality. -/
theorem idempotentImage_projector_sum (n : ι) :
    (∑ j : Fin (N n + 1), (factorThruImage (e j.val)).f n ≫ (image.ι (e j.val)).f n) =
      𝟙 (K.X n) := by
  simp only [← HomologicalComplex.comp_f, image.fac]
  exact hsum n

include he hsupport hsum in
/-- Let C be an abelian category with countable coproducts and
K a complex of arbitrary shape. Suppose orthogonal idempotents e_j
vanish in degree n for j > N(n), and their components up to N(n)
sum to id_(K_n). The image inclusions induce the complex isomorphism
⨁_(j∈ℕ) Im(e_j) ≅ K. Its degreewise inverse is the finite sum of
the image factors followed by coproduct inclusions. -/
def locallyFiniteIdempotentImageComplexIso : (∐ (fun j : ℕ => image (e j))) ≅ K :=
  locallyFiniteSplitComplexCoproductIso K (fun j : ℕ => image (e j))
    (fun j => image.ι (e j)) (fun j => factorThruImage (e j))
    (idempotentImage_split K e he) (idempotentImage_cross K e he) N
    (idempotentImage_factor_support K e N hsupport)
    (idempotentImage_projector_sum K e N hsum)

include he hsupport hsum in
/-- Let C be an abelian category with countable coproducts and
K a complex of arbitrary shape with orthogonal idempotents e_j.
Assume (e_j)_n = 0 for j > N(n) and
∑_(j=0)^(N(n)) (e_j)_n = id_(K_n) in every degree.
Then ⨁_j H_n(Im(e_j)) ≅ H_n(K), with forward map induced by image
inclusions and inverse ∑_(j=0)^(N(n)) ι_j ∘ H_n(p_j). -/
def locallyFiniteIdempotentImageHomologyIso (n : ι) :
    (∐ (fun j : ℕ => (image (e j)).homology n)) ≅ K.homology n :=
  finiteSplitHomologyCoproductIso K (fun j : ℕ => image (e j))
    (fun j => image.ι (e j)) (fun j => factorThruImage (e j))
    (idempotentImage_split K e he) (idempotentImage_cross K e he) n (N n)
    (idempotentImage_factor_support K e N hsupport n)
    (idempotentImage_projector_sum K e N hsum n)

end HomologicalComplex
