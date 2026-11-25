/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The shuffle product identity for path signatures

The shuffle product `I ⧢ J` of two words is the multiset of all interleavings of `I` and `J`
that keep the internal order of each (Chevyrev–Kormilitzin, *A primer on the signature method in
machine learning*, arXiv:1603.03788v2, Definition 1.12). We represent it as a list of words,
repetitions included, defined by the last-letter recursion
`(I i) ⧢ (J j) = (I ⧢ J j) i + (I i ⧢ J) j`, `∅ ⧢ J = J`, `I ⧢ ∅ = I`.

Ree's shuffle product identity (primer, Theorem 1.14; Lyons, ICM 2014, Lemma 9.3) says that the
product of two iterated integrals of a path is the sum of the iterated integrals along the
shuffles: `S^I_{s,t} · S^J_{s,t} = ∑_{K ∈ I ⧢ J} S^K_{s,t}`. We prove it for paths with
continuous velocity (continuously differentiable paths), by the product rule and the fundamental
theorem of calculus.
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace MathlibExt.Analysis.PathSignature

variable {ι : Type*}

/-- **Shuffle product of two words.** `shuffle I J` lists, with multiplicity, every word obtained by
interleaving `I` and `J` while preserving the order of the letters of each; it has
`(|I| + |J| choose |I|)` entries (Chevyrev and Kormilitzin, *A primer on the signature method in
machine learning*, arXiv:1603.03788v2, Definition 1.12). It satisfies `∅ ⧢ J = J`, `I ⧢ ∅ = I`
and the last-letter recursion `(I i) ⧢ (J j) = (I ⧢ J j) i + (I i ⧢ J) j`
(the decomposition used in the proof of Theorem 1.14 there). -/
def shuffle (I J : List ι) : List (List ι) :=
  (go I.reverse J.reverse).map List.reverse
where
  /- Shuffles of reversed words, by first-letter recursion. -/
  go : List ι → List ι → List (List ι)
    | [], v => [v]
    | a :: u, [] => [a :: u]
    | a :: u, b :: v => (go u (b :: v)).map (a :: ·) ++ (go (a :: u) v).map (b :: ·)
  termination_by u v => u.length + v.length

@[simp] theorem shuffle_nil_left (J : List ι) : shuffle [] J = [J] := by
  simp [shuffle, shuffle.go]

private theorem shuffle_go_nil_right (u : List ι) : shuffle.go u [] = [u] := by
  cases u <;> simp [shuffle.go]

@[simp] theorem shuffle_nil_right (I : List ι) : shuffle I [] = [I] := by
  simp [shuffle, shuffle_go_nil_right]

/-- **Last-letter recursion of the shuffle product.**
`(I i) ⧢ (J j) = (I ⧢ J j) i + (I i ⧢ J) j` (Chevyrev and Kormilitzin, arXiv:1603.03788v2,
the "combination identity" in the proof of Theorem 1.14). -/
theorem shuffle_concat_concat (I J : List ι) (i j : ι) :
    shuffle (I ++ [i]) (J ++ [j]) =
      (shuffle I (J ++ [j])).map (· ++ [i]) ++ (shuffle (I ++ [i]) J).map (· ++ [j]) := by
  simp only [shuffle, List.reverse_append, List.reverse_singleton, List.singleton_append]
  rw [shuffle.go]
  simp [List.map_map, Function.comp_def]

variable {v : ι → ℝ → ℝ}

private theorem integral_list_sum_mul {s : ℝ} {i : ι}
    (hcont : ∀ K : List ι, Continuous fun t => signature v s t K)
    (hv : Continuous (v i)) (L : List (List ι)) (t : ℝ) :
    ∫ u in s..t, (L.map fun K => signature v s u K).sum * v i u =
      (L.map fun K => ∫ u in s..t, signature v s u K * v i u).sum := by
  induction L with
  | nil => simp
  | cons K L ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    have h1 : IntervalIntegrable (fun u => signature v s u K * v i u) volume s t :=
      ((hcont K).mul hv).intervalIntegrable s t
    have h2 : IntervalIntegrable (fun u => (L.map fun K => signature v s u K).sum * v i u)
        volume s t :=
      ((continuous_list_sum _ fun K _ => hcont K).mul hv).intervalIntegrable s t
    rw [intervalIntegral.integral_add h1 h2, ih]

/-- **Shuffle product identity (Ree).** For a path whose velocity components are continuous, and
any two words `I, J`, the product of the iterated integrals along `I` and `J` is the sum of the
iterated integrals along the shuffles of `I` and `J`:
`S^I_{s,t} · S^J_{s,t} = ∑_{K ∈ I ⧢ J} S^K_{s,t}` (Chevyrev and Kormilitzin, *A primer on the
signature method in machine learning*, arXiv:1603.03788v2, Theorem 1.14, equation (13);
T. Lyons, *Rough paths, signatures and the modelling of functions on streams*, Proc. ICM 2014,
arXiv:1405.4537, Lemma 9.3). Hence the linear functionals `S ↦ S^I` of the signature span an
algebra under pointwise multiplication. -/
theorem signature_mul_signature (hv : ∀ i, Continuous (v i)) (s t : ℝ) (I J : List ι) :
    signature v s t I * signature v s t J =
      ((shuffle I J).map fun K => signature v s t K).sum := by
  have hcont : ∀ K : List ι, Continuous fun t => signature v s t K :=
    continuous_signature (fun i a b => (hv i).intervalIntegrable a b) s
  induction I using List.reverseRecOn generalizing J t with
  | nil => simp
  | append_singleton I i ihI =>
    induction J using List.reverseRecOn generalizing t with
    | nil => simp
    | append_singleton J j ihJ =>
      -- Product rule and the fundamental theorem of calculus for `F · G`.
      have hderiv : ∀ x ∈ Set.uIcc s t, HasDerivAt
          (fun t => signature v s t (I ++ [i]) * signature v s t (J ++ [j]))
          (signature v s x I * v i x * signature v s x (J ++ [j]) +
            signature v s x (I ++ [i]) * (signature v s x J * v j x)) x := fun x _ =>
        HasDerivAt.mul (hasDerivAt_signature_concat hv s I i x)
          (hasDerivAt_signature_concat hv s J j x)
      have hint : IntervalIntegrable (fun x =>
          signature v s x I * v i x * signature v s x (J ++ [j]) +
            signature v s x (I ++ [i]) * (signature v s x J * v j x)) volume s t := by
        exact ((((hcont I).mul (hv i)).mul (hcont _)).add
          ((hcont _).mul ((hcont J).mul (hv j)))).intervalIntegrable _ _
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      simp only [signature_self, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
        ite_false, mul_zero, sub_zero] at hFTC
      rw [← hFTC]
      have hrw : ∀ x, signature v s x I * v i x * signature v s x (J ++ [j]) +
            signature v s x (I ++ [i]) * (signature v s x J * v j x) =
          ((shuffle I (J ++ [j])).map fun K => signature v s x K).sum * v i x +
            ((shuffle (I ++ [i]) J).map fun K => signature v s x K).sum * v j x := by
        intro x
        rw [← ihI x (J ++ [j]), ← ihJ x]
        ring
      simp_rw [hrw]
      rw [intervalIntegral.integral_add, integral_list_sum_mul hcont (hv i),
        integral_list_sum_mul hcont (hv j), shuffle_concat_concat, List.map_append,
        List.sum_append, List.map_map, List.map_map]
      · simp [Function.comp_def, signature_concat]
      · exact (((continuous_list_sum _ fun K _ => hcont K)).mul (hv i)).intervalIntegrable _ _
      · exact (((continuous_list_sum _ fun K _ => hcont K)).mul (hv j)).intervalIntegrable _ _

/-- **Lévy area.** For letters `i, j`, the signed area
`A^{ij}_{s,t} = ½ (S^{ij}_{s,t} − S^{ji}_{s,t})` enclosed by the plane path `(Xⁱ, Xʲ)` on
`[s, t]` and the chord joining its endpoints (Chevyrev and Kormilitzin, *A primer on the
signature method in machine learning*, arXiv:1603.03788v2, §1.2.4, equation (12)). -/
noncomputable def levyArea (v : ι → ℝ → ℝ) (s t : ℝ) (i j : ι) : ℝ :=
  (signature v s t [i, j] - signature v s t [j, i]) / 2

/-- **Second level of the signature: increments and Lévy area.** For a path with continuous
velocity, `S^{ij}_{s,t} = ½ (Xⁱ_t − Xⁱ_s)(Xʲ_t − Xʲ_s) + A^{ij}_{s,t}`: the symmetric part of the
second level is determined by the increment, and the antisymmetric part is the Lévy area. This
follows from the shuffle identity `S^i S^j = S^{ij} + S^{ji}` (Chevyrev and Kormilitzin,
arXiv:1603.03788v2, Example 1.15 and equation (12)). -/
theorem signature_pair_eq (hv : ∀ i, Continuous (v i)) (s t : ℝ) (i j : ι) :
    signature v s t [i, j] =
      (∫ u in s..t, v i u) * (∫ u in s..t, v j u) / 2 + levyArea v s t i j := by
  have h := signature_mul_signature hv s t [i] [j]
  have hs : shuffle [i] [j] = [[j, i], [i, j]] := by
    simp [shuffle, shuffle.go]
  rw [hs, signature_singleton, signature_singleton] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  unfold levyArea
  linarith

end MathlibExt.Analysis.PathSignature
