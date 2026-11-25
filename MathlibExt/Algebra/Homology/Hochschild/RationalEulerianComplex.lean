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
# Rational Eulerian chain maps and decomposition

Coefficient-fixed rational permutation
operators give finite complete orthogonal
Eulerian chain projectors. Their locally
finite images decompose the complex
and homology without coefficient flatness
or projectivity. The rational parameter
family is convolution bar-lambda; the
integer lambda convention retains its
separate integer sign.
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

/-- The coefficient-fixed rational convolution operation. -/
def rationalConvolutionOperator (n : ℕ) (a : ℚ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
    (Equiv.Perm.eulerianLambda n a)

/-- Its finite expansion has the original Eulerian coefficients. -/
theorem rationalConvolutionOperator_eq_sum (n : ℕ) (a : ℚ) :
    rationalConvolutionOperator k A M n a =
      ∑ i : Fin (n + 1), algebraMap ℚ k (a ^ i.val) • coefficientEulerianOperator k A M n i.val := by
  rw [rationalConvolutionOperator, Equiv.Perm.eulerianLambda_eq_sum, map_sum]
  simp only [TensorPower.coefficientRationalPermutationAction_smul, coefficientEulerianOperator]

/-- The stable-sort convolution polynomial family composes by multiplying its rational parameters. -/
theorem rationalConvolutionOperator_comp (n : ℕ) (a b : ℚ) :
    (rationalConvolutionOperator k A M n a).comp (rationalConvolutionOperator k A M n b) =
      rationalConvolutionOperator k A M n (a * b) := by
  change TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
      (Equiv.Perm.eulerianLambda n a) *
    TensorPower.coefficientRationalPermutationAction (M := M) (V := A) n
      (Equiv.Perm.eulerianLambda n b) = _
  rw [← map_mul, Equiv.Perm.eulerianLambda_mul]
  rfl

/-- Every rational convolution value commutes with the complete original boundary. -/
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

/-- The convolution parameter family is a native chain endomorphism. -/
def rationalConvolutionChainMap (a : ℚ) : chainComplex k A M ⟶ chainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (rationalConvolutionOperator k A M n a)) (by
    intro n
    apply ModuleCat.hom_ext
    exact rationalConvolutionOperator_boundary k A M n a)

/-- The parameter chain map retains the original coefficient-fixed degree operator. -/
theorem rationalConvolutionChainMap_f (n : ℕ) (a : ℚ) :
    ((rationalConvolutionChainMap k A M a).f n).hom = rationalConvolutionOperator k A M n a := rfl

/-- Loday's original true integer lambda, as a native map of the Hochschild complex. -/
def trueIntegerLambdaChainMap (m : ℕ) (_hm : 0 < m) : chainComplex k A M ⟶ chainComplex k A M :=
  (-1 : k) ^ (m - 1) • rationalConvolutionChainMap k A M (m : ℚ)

/-- Its component is the neutral integral true-lambda action on the original words. -/
theorem trueIntegerLambdaChainMap_f (n m : ℕ) (hm : 0 < m) :
    ((trueIntegerLambdaChainMap k A M m hm).f n).hom =
      TensorPower.coefficientTrueIntegerLambdaOperator (M := M) (V := A) n m hm := by
  rw [trueIntegerLambdaChainMap, HomologicalComplex.smul_f_apply, ModuleCat.hom_smul,
    TensorPower.coefficientTrueIntegerLambdaOperator_eq_eulerian]
  rfl

/-- The true integer maps retain the positive-parameter parity in native chain composition. -/
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

/-- Native chain composition retains the convolution parameter multiplication law. -/
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

/-- The Eulerian summand is the native image of the original chain projector. -/
def eulerianImageComplex (i : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  image (eulerianChainMap k A M i)

/-- The original sum of image inclusions is a native all-degree Hodge isomorphism. -/
def hodgeComplexIso : (∐ (fun i : ℕ => eulerianImageComplex k A M i)) ≅ chainComplex k A M :=
  HomologicalComplex.locallyFiniteIdempotentImageComplexIso
    (chainComplex k A M) (eulerianChainMap k A M) (eulerianChainMap_comp k A M) id
    (eulerianChainMap_support k A M) (eulerianChainMap_sum k A M)

/-- The forward isomorphism is exactly the native sum of the original image inclusions. -/
theorem hodgeComplexIso_hom :
    (hodgeComplexIso k A M).hom = Sigma.desc (fun i => image.ι (eulerianChainMap k A M i)) := rfl

/-- The image homologies have the original finite-projection coproduct decomposition. -/
def hodgeHomologyIso (n : ℕ) :
    (∐ (fun i : ℕ => (eulerianImageComplex k A M i).homology n)) ≅ (chainComplex k A M).homology n :=
  HomologicalComplex.locallyFiniteIdempotentImageHomologyIso
    (chainComplex k A M) (eulerianChainMap k A M) (eulerianChainMap_comp k A M) id
    (eulerianChainMap_support k A M) (eulerianChainMap_sum k A M) n

/-- The original image inclusion homology maps form the Hodge decomposition map. -/
theorem hodgeHomologyIso_hom (n : ℕ) :
    (hodgeHomologyIso k A M n).hom = Sigma.desc
      (fun i => HomologicalComplex.homologyMap (image.ι (eulerianChainMap k A M i)) n) := rfl

/-- Actual coefficient-fixed Hodge projection on the original Hochschild homology. -/
def eulerianHomologyProjector (n i : ℕ) : (chainComplex k A M).homology n ⟶ (chainComplex k A M).homology n :=
  HomologicalComplex.homologyMap (eulerianChainMap k A M i) n

/-- The original Hodge homology projections satisfy the orthogonal projector law. -/
theorem eulerianHomologyProjector_comp (n i j : ℕ) :
    eulerianHomologyProjector k A M n i ≫ eulerianHomologyProjector k A M n j =
      if i = j then eulerianHomologyProjector k A M n i else 0 := by
  rw [eulerianHomologyProjector, eulerianHomologyProjector, ← HomologicalComplex.homologyMap_comp,
    eulerianChainMap_comp]
  split_ifs with h
  · rfl
  · exact HomologicalComplex.homologyMap_zero
      (K := chainComplex k A M) (L := chainComplex k A M) (i := n)

/-- The original rational convolution family on the Hochschild homology. -/
def rationalConvolutionHomologyMap (n : ℕ) (a : ℚ) :
    (chainComplex k A M).homology n ⟶ (chainComplex k A M).homology n :=
  HomologicalComplex.homologyMap (rationalConvolutionChainMap k A M a) n

/-- Native homology composition retains the proved original convolution parameter multiplication. -/
theorem rationalConvolutionHomologyMap_comp (n : ℕ) (a b : ℚ) :
    rationalConvolutionHomologyMap k A M n a ≫ rationalConvolutionHomologyMap k A M n b =
      rationalConvolutionHomologyMap k A M n (a * b) := by
  simp only [rationalConvolutionHomologyMap, ← HomologicalComplex.homologyMap_comp,
    rationalConvolutionChainMap_comp]

end ModuleCat.Algebra.Hochschild.Symmetric
