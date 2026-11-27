/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.EulerianChainMaps
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianBoundary
public import MathlibExt.Algebra.Homology.LocallyFiniteIdempotentImages
public import MathlibExt.Combinatorics.Perm.EulerianRationalFamily
public import MathlibExt.LinearAlgebra.TensorPower.IntegralEulerianComparison

/-!
# Rational Eulerian operations and the coefficient Hodge decomposition

Let k be a commutative ℚ-algebra, A a commutative k-algebra and M an
A-module with a compatible k-module structure. The symmetric coefficient
Hochschild complex has terms C_n(A,M) = M ⊗[k] A^⊗n and the full
alternating Hochschild boundary. Rational Eulerian operators act on its
algebra factors and fix the coefficient. Their projectors e_n^(i) are
orthogonal, vanish for i > n and sum to the identity for 0 ≤ i ≤ n.

The rational convolution family is
Λ_n(a) = ∑_(i=0)^n a^i e_n^(i), a ∈ ℚ.
It satisfies Λ_n(a)Λ_n(b) = Λ_n(ab) and commutes with the boundary.
For a positive integer m, the signed integer convention is
λ_n^m = (−1)^(m−1)Λ_n(m); its composition law has the extra factor
(−1)^((l−1)(m−1)).

Writing C^(i) for the image complex of the ith Eulerian chain projector,
the image inclusions give ⨁_(i∈ℕ) C^(i) ≅ C and
⨁_(i∈ℕ) H_n(C^(i)) ≅ H_n(C). The sum is locally finite in each
degree. All maps here are k-linear, in ModuleCat^max(u,v,w)(k), with
independent worlds of k, A and M. No coefficient flatness or
projectivity is required.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a k-module M, n ≥ 0 and a ∈ ℚ, Λ_n(a) is the k-linear permutation
operator on M ⊗[k] A^⊗n associated with the rational Eulerian
polynomial Λ_n(a). It fixes M and permutes only the n algebra factors. -/
def rationalConvolutionOperator (n : ℕ) (a : ℚ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
    (Equiv.Perm.eulerianLambda n a)

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a k-module, the coefficient-fixed convolution operator satisfies
Λ_n(a) = ∑_(i=0)^n algebraMap(a^i) e_n^(i) for every a ∈ ℚ.
The coefficients act by the ground k-module structure on
M ⊗[k] A^⊗n. -/
theorem rationalConvolutionOperator_eq_sum (n : ℕ) (a : ℚ) :
    rationalConvolutionOperator k A M n a =
      ∑ i : Fin (n + 1), algebraMap ℚ k (a ^ i.val) • coefficientEulerianOperator k A M n i.val := by
  rw [rationalConvolutionOperator, Equiv.Perm.eulerianLambda_eq_sum, map_sum]
  simp only [TensorPower.coefficientRationalPermutationAction_smul, coefficientEulerianOperator]

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
a k-module M, the degree-n coefficient-fixed operators satisfy
Λ_n(a) ∘ Λ_n(b) = Λ_n(ab) for all a,b ∈ ℚ.
This equality of k-linear maps does not require an A-action on M. -/
theorem rationalConvolutionOperator_comp (n : ℕ) (a b : ℚ) :
    (rationalConvolutionOperator k A M n a).comp (rationalConvolutionOperator k A M n b) =
      rationalConvolutionOperator k A M n (a * b) := by
  change TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
      (Equiv.Perm.eulerianLambda n a) *
    TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
      (Equiv.Perm.eulerianLambda n b) = _
  rw [← map_mul, Equiv.Perm.eulerianLambda_mul]
  rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
an A-module M with compatible ground action, the boundary
b_n : C_(n+1)(A,M) → C_n(A,M) satisfies
b_n ∘ Λ_(n+1)(a) = Λ_n(a) ∘ b_n for every n ≥ 0 and a ∈ ℚ.
The first and last coefficient faces are included. -/
theorem rationalConvolutionOperator_boundary (n : ℕ) (a : ℚ) :
    ((chainComplex k A M).d (n + 1) n).hom.comp
        (rationalConvolutionOperator k A M (n + 1) a) =
      (rationalConvolutionOperator k A M n a).comp ((chainComplex k A M).d (n + 1) n).hom := by
  let d : M ⊗[k] TensorPower k (n + 1) A →ₗ[k] M ⊗[k] TensorPower k n A :=
    (algebraBoundary k A M n).restrictScalars k
  change d.comp (rationalConvolutionOperator k A M (n + 1) a) =
    (rationalConvolutionOperator k A M n a).comp d
  rw [rationalConvolutionOperator_eq_sum, rationalConvolutionOperator_eq_sum]
  apply LinearMap.ext
  intro x
  have hd (i : ℕ) : d.comp (coefficientEulerianOperator k A M (n + 1) i) =
      (coefficientEulerianOperator k A M n i).comp d := coefficientEulerian_boundary k A M n i
  have hcomm (i : ℕ) : d (coefficientEulerianOperator k A M (n + 1) i x) =
      coefficientEulerianOperator k A M n i (d x) :=
    congrArg (fun f : M ⊗[k] TensorPower k (n + 1) A →ₗ[k] M ⊗[k] TensorPower k n A => f x) (hd i)
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  simp_rw [hcomm]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last,
    coefficientEulerian_outside k A M n (n + 1) (by omega),
    LinearMap.zero_apply, smul_zero, add_zero]

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M an A-module with compatible k-action, the operators Λ_n(a), n ≥ 0,
define a chain endomorphism of C_*(A,M) for every a ∈ ℚ.
Each component fixes the coefficient and acts on the algebra factors. -/
def rationalConvolutionChainMap (a : ℚ) : chainComplex k A M ⟶ chainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (rationalConvolutionOperator k A M n a)) (by
    intro n
    apply ModuleCat.hom_ext
    exact rationalConvolutionOperator_boundary k A M n a)

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
a compatible A-module M, the degree-n component of the rational
convolution chain map with parameter a ∈ ℚ is the k-linear operator
Λ_n(a) on M ⊗[k] A^⊗n. -/
theorem rationalConvolutionChainMap_f (n : ℕ) (a : ℚ) :
    ((rationalConvolutionChainMap k A M a).f n).hom = rationalConvolutionOperator k A M n a := rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and m > 0, the integer lambda chain map on
C_*(A,M) is (−1)^(m−1)Λ(m). The sign depends on the positive
integer parameter m, while Λ(m) is the rational convolution map. -/
def trueIntegerLambdaChainMap (m : ℕ) (_hm : 0 < m) : chainComplex k A M ⟶ chainComplex k A M :=
  (-1 : k) ^ (m - 1) • rationalConvolutionChainMap k A M (m : ℚ)

/-- For k a commutative ℚ-algebra, A a commutative k-algebra,
M a compatible A-module and m > 0, the degree-n component of the
signed integer lambda chain map equals the integral coefficient-fixed
operator λ_n^m on M ⊗[k] A^⊗n.
Its convention is λ_n^m = (−1)^(m−1)Λ_n(m). -/
theorem trueIntegerLambdaChainMap_f (n m : ℕ) (hm : 0 < m) :
    ((trueIntegerLambdaChainMap k A M m hm).f n).hom =
      TensorPower.coefficientTrueIntegerLambdaOperator (M := M) (V := A) n m hm := by
  rw [trueIntegerLambdaChainMap, HomologicalComplex.smul_f_apply, ModuleCat.hom_smul,
    TensorPower.coefficientTrueIntegerLambdaOperator_eq_eulerian]
  rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and l,m > 0, applying λ^l and then λ^m
on the coefficient Hochschild complex gives
λ^m ∘ λ^l = (−1)^((l−1)(m−1)) λ^(lm).
The scalar sign is part of the signed integer convention. -/
theorem trueIntegerLambdaChainMap_comp (l m : ℕ) (hl : 0 < l) (hm : 0 < m) :
    trueIntegerLambdaChainMap k A M l hl ≫ trueIntegerLambdaChainMap k A M m hm =
      (-1 : k) ^ ((l - 1) * (m - 1)) •
        trueIntegerLambdaChainMap k A M (l * m) (Nat.mul_pos hl hm) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.smul_f_apply, ModuleCat.hom_comp,
    ModuleCat.hom_smul, trueIntegerLambdaChainMap_f]
  change (TensorPower.coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := A) n m hm).comp
      (TensorPower.coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := A) n l hl) =
    (-1 : k) ^ ((l - 1) * (m - 1)) •
      TensorPower.coefficientTrueIntegerLambdaOperator (k := k) (M := M) (V := A) n (l * m) (Nat.mul_pos hl hm)
  simpa only [Nat.mul_comm m l, Nat.mul_comm (m - 1) (l - 1)] using
    TensorPower.coefficientTrueIntegerLambdaOperator_comp (k := k) (M := M) (V := A) n m l hm hl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and a,b ∈ ℚ, applying the chain maps Λ(a)
and then Λ(b) gives Λ(ab). Thus Λ(b) ∘ Λ(a) = Λ(ab) as
endomorphisms of C_*(A,M). -/
theorem rationalConvolutionChainMap_comp (a b : ℚ) :
    rationalConvolutionChainMap k A M a ≫ rationalConvolutionChainMap k A M b =
      rationalConvolutionChainMap k A M (a * b) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, rationalConvolutionChainMap_f]
  change (rationalConvolutionOperator k A M n b).comp (rationalConvolutionOperator k A M n a) =
    rationalConvolutionOperator k A M n (a * b)
  simpa only [mul_comm] using rationalConvolutionOperator_comp k A M n b a

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, C^(i) is the categorical image of the
ith Eulerian chain projector on C_*(A,M).
It is an ℕ-indexed chain complex in ModuleCat^max(u,v,w)(k). -/
def eulerianImageComplex (i : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  image (eulerianChainMap k A M i)

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
a compatible A-module M, the sum of Eulerian image inclusions gives
the k-linear chain isomorphism ⨁_(i∈ℕ) C^(i) ≅ C_*(A,M).
The degree-n projectors vanish for i > n and sum to the identity
over 0 ≤ i ≤ n. -/
def hodgeComplexIso : (∐ (fun i : ℕ => eulerianImageComplex k A M i)) ≅ chainComplex k A M :=
  HomologicalComplex.locallyFiniteIdempotentImageComplexIso
    (chainComplex k A M) (eulerianChainMap k A M) (eulerianChainMap_comp k A M) id
    (eulerianChainMap_support k A M) (eulerianChainMap_sum k A M)

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the forward map of
⨁_i C^(i) ≅ C_*(A,M) is the coproduct map whose ith restriction
is the image inclusion C^(i) → C_*(A,M). -/
theorem hodgeComplexIso_hom :
    (hodgeComplexIso k A M).hom = Sigma.desc (fun i => image.ι (eulerianChainMap k A M i)) := rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and n ≥ 0, there is a k-module isomorphism
⨁_(i∈ℕ) H_n(C^(i)) ≅ H_n(C_*(A,M)).
It is induced by the locally finite complete family of orthogonal
Eulerian chain projectors. -/
def hodgeHomologyIso (n : ℕ) :
    (∐ (fun i : ℕ => (eulerianImageComplex k A M i).homology n)) ≅ (chainComplex k A M).homology n :=
  HomologicalComplex.locallyFiniteIdempotentImageHomologyIso
    (chainComplex k A M) (eulerianChainMap k A M) (eulerianChainMap_comp k A M) id
    (eulerianChainMap_support k A M) (eulerianChainMap_sum k A M) n

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, the forward Eulerian decomposition in degree
n is the coproduct map with ith restriction
H_n(C^(i) → C_*(A,M)), the homology map of the image inclusion. -/
theorem hodgeHomologyIso_hom (n : ℕ) :
    (hodgeHomologyIso k A M n).hom = Sigma.desc
      (fun i => HomologicalComplex.homologyMap (image.ι (eulerianChainMap k A M i)) n) := rfl

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and n,i ≥ 0, the ith Eulerian homology
projector is H_n(e^(i)), the endomorphism of H_n(C_*(A,M)) induced
by the coefficient-fixed Eulerian chain projector. -/
def eulerianHomologyProjector (n i : ℕ) : (chainComplex k A M).homology n ⟶ (chainComplex k A M).homology n :=
  HomologicalComplex.homologyMap (eulerianChainMap k A M i) n

/-- For a commutative ℚ-algebra k, a commutative k-algebra A and
a compatible A-module M, the homology projectors satisfy
E_j ∘ E_i = E_i when i = j and zero when i ≠ j, in every degree n.
Here E_i = H_n(e^(i)) on H_n(C_*(A,M)). -/
theorem eulerianHomologyProjector_comp (n i j : ℕ) :
    eulerianHomologyProjector k A M n i ≫ eulerianHomologyProjector k A M n j =
      if i = j then eulerianHomologyProjector k A M n i else 0 := by
  rw [eulerianHomologyProjector, eulerianHomologyProjector, ← HomologicalComplex.homologyMap_comp,
    eulerianChainMap_comp]
  split_ifs with h
  · rfl
  · exact HomologicalComplex.homologyMap_zero
      (K := chainComplex k A M) (L := chainComplex k A M) (i := n)

/-- For k a commutative ℚ-algebra, A a commutative k-algebra and
M a compatible A-module, H_n(Λ(a)) is the endomorphism of coefficient
Hochschild homology induced by the rational convolution chain map,
for every n ≥ 0 and a ∈ ℚ. -/
def rationalConvolutionHomologyMap (n : ℕ) (a : ℚ) :
    (chainComplex k A M).homology n ⟶ (chainComplex k A M).homology n :=
  HomologicalComplex.homologyMap (rationalConvolutionChainMap k A M a) n

/-- For a commutative ℚ-algebra k, a commutative k-algebra A,
a compatible A-module M and a,b ∈ ℚ, the induced homology maps
satisfy H_n(Λ(b)) ∘ H_n(Λ(a)) = H_n(Λ(ab)) in every n ≥ 0. -/
theorem rationalConvolutionHomologyMap_comp (n : ℕ) (a b : ℚ) :
    rationalConvolutionHomologyMap k A M n a ≫ rationalConvolutionHomologyMap k A M n b =
      rationalConvolutionHomologyMap k A M n (a * b) := by
  simp only [rationalConvolutionHomologyMap, ← HomologicalComplex.homologyMap_comp,
    rationalConvolutionChainMap_comp]

end ModuleCat.Algebra.Hochschild.Symmetric
