/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.RandomTranspositionEstimates
import MathlibExt.Probability.RandomTranspositionRank
import MathlibExt.Probability.GroupWalkTrace
public import MathlibExt.Probability.RandomTranspositionLower
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The upper cutoff bound for random transpositions

On functions on the symmetric group, average over permutations fixing a specified set of `j`
positions. Each such average depends only on the images of those positions. The symmetriser
bounds on the transposition operator and the resulting dimension estimate control the positive
spectrum; multiplying functions by the permutation sign controls the negative spectrum.
The even-time trace bound then gives the estimate in total variation.

The lemma
`MathlibExt.Probability.RandomWalkFiniteGroup.upper_bound_lemma`
and the transform `fourier_randomTransposition` give the character formulation. The lower bound
`diaconis_shahshahani_lower` is in the imported module. The Bayer–Diaconis formula for riffle
shuffles is `MathlibExt.Probability.RiffleShuffle.card_sort_eq`.

Diaconis and Shahshahani use the `ℓ¹` norm, twice `MathlibExt.Probability.MarkovMixing.tvDist`;
the Saint-Flour notes use total variation. See Diaconis and Shahshahani, *Generating a random
permutation with random transpositions* (1981), Theorem 1, for the character-theoretic proof.
-/

open Matrix Module Equiv WithLp
open MathlibExt.Probability.RandomWalkFiniteGroup
open MathlibExt.Probability.RandomTranspositionFiltration
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (convPow)
open MathlibExt.Probability.MarkovMixing (tvDist)

namespace MathlibExt.Probability.RandomTranspositionUpper

private abbrev G (n : ℕ) := Equiv.Perm (Fin n)
private noncomputable abbrev A (n : ℕ) [NeZero n] := walkMatrix (randomTransposition n)

private theorem hermitian (n : ℕ) [NeZero n] : (A n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  simpa [A, walkMatrix] using randomTransposition_inv n (x * y⁻¹)

private theorem transSum_eq {n : ℕ} [NeZero n] (f : G n → ℝ) :
    transSum Finset.univ f = (n : ℝ) ^ 2 • ((A n) *ᵥ f) := by
  classical
  funext x
  have h (y : G n) : randomTransposition n (x * y⁻¹) = randomTransposition n (x⁻¹ * y) := by
    calc
      _ = randomTransposition n (y⁻¹ * x) := by
        simpa [mul_assoc] using randomTransposition_conj n (y⁻¹ * x) x
      _ = _ := by simpa using randomTransposition_inv n (x⁻¹ * y)
  simp only [transSum, Pi.smul_apply, smul_eq_mul, A, walkMatrix, Matrix.mulVec, dotProduct,
    h, randomTransposition_eq_expect, Finset.expect_mul, ← Finset.expect_sum_comm]
  have he (i j : Fin n) (y : G n) : swap i j = x⁻¹ * y ↔ x * swap i j = y :=
    eq_inv_mul_iff_mul_eq
  simp_rw [he, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [Fintype.expect_eq_sum_div_card, ← Finset.sum_div, div_div, sq]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp [hn]

private noncomputable def signReal {n : ℕ} (x : G n) : ℝ := (x.sign : ℤ)

private theorem signReal_sq {n : ℕ} (x : G n) : signReal x * signReal x = 1 := by
  rcases Int.units_eq_one_or x.sign with h | h <;> simp [signReal, h]

private noncomputable def signMap (n : ℕ) : (G n → ℝ) →ₗ[ℝ] (G n → ℝ) where
  toFun f x := signReal x * f x
  map_add' f g := by ext; simp [mul_add]
  map_smul' t f := by ext; simp; ring

private theorem signMap_inj (n : ℕ) : Function.Injective (signMap n) := by
  intro f g h
  have h2 := congrArg (signMap n) h
  simpa only [signMap, LinearMap.coe_mk, AddHom.coe_mk, ← mul_assoc, signReal_sq, one_mul] using h2

private theorem transSum_signMap {n : ℕ} (f : G n → ℝ) :
    transSum Finset.univ (signMap n f) =
      (2 * (n : ℝ)) • signMap n f - signMap n (transSum Finset.univ f) := by
  funext x
  have he (i j : Fin n) : signReal (x * swap i j) * f (x * swap i j) =
      (if i = j then 2 * signReal x * f x else 0) - signReal x * f (x * swap i j) := by
    by_cases h : i = j
    · subst j; rw [Equiv.swap_self, ← Perm.one_def]; simp; ring
    · simp [signReal, map_mul, Equiv.Perm.sign_swap h, h]
  simp only [transSum, signMap, LinearMap.coe_mk, AddHom.coe_mk, he, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  ring

private theorem twist_eigen {n : ℕ} [NeZero n] {f : G n → ℝ} {b : ℝ} (hf : A n *ᵥ f = b • f) :
    A n *ᵥ signMap n f = (2 / n - b) • signMap n f := by
  have h := transSum_signMap f
  rw [transSum_eq, transSum_eq, hf, smul_smul, map_smul] at h
  funext x
  have hh := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hh ⊢
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp
  apply mul_left_cancel₀ hn
  linear_combination hh

private theorem tvBound (n k : ℕ) [NeZero n] :
    2 * tvDist (convPow (randomTransposition n) k) (uniform (G n)) ≤ 2 := by
  have h (x : G n) : |convPow (randomTransposition n) k x - uniform (G n) x| ≤
      convPow (randomTransposition n) k x + uniform (G n) x := by
    have h0 : 0 ≤ uniform (G n) x := by unfold uniform; positivity
    exact abs_le.mpr ⟨by linarith [randomTransposition_convPow_nonneg k x], by linarith⟩
  have hh := Finset.sum_le_sum (s := Finset.univ) fun x _ => h x
  simp only [Finset.sum_add_distrib, sum_randomTransposition_convPow] at hh
  have hU : ∑ x : G n, uniform _ x = 1 := by simp [uniform]
  rw [hU] at hh
  unfold tvDist
  linarith


/-- An eigenvector of a self-adjoint map is orthogonal to an invariant subspace on which
its eigenvalue is absent. -/
private theorem orthogonal_of_no_eigenvector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (K : Submodule ℝ E) (hK : ∀ v ∈ K, T v ∈ K) {b : ℝ} {x : E} (hx : T x = b • x)
    (hn : ∀ v ∈ K, T v = b • v → v = 0) : x ∈ Kᗮ := by
  let S : K →ₗ[ℝ] K := T.restrict hK - b • LinearMap.id
  have hinj : Function.Injective S := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro v hv
    apply Subtype.ext
    apply hn v v.2
    exact sub_eq_zero.mp (congrArg Subtype.val hv)))
  intro y hy
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj ⟨y, hy⟩
  change inner ℝ y x = 0
  have h : T (v : E) - b • (v : E) = y := congrArg Subtype.val hv
  rw [← h, inner_sub_left, hT, hx, real_inner_smul_left, real_inner_smul_right, sub_self]

private theorem card_eigenvectors_le_codim {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (K : Submodule ℝ E) (hK : ∀ v ∈ K, T v ∈ K) {ι : Type*} [Fintype ι]
    (v : ι → E) (hv : LinearIndependent ℝ v) (b : ι → ℝ) (hb : ∀ i, T (v i) = b i • v i)
    (hn : ∀ i w, w ∈ K → T w = b i • w → w = 0) :
    Fintype.card ι + finrank ℝ K ≤ finrank ℝ E := by
  let w (i : ι) : Kᗮ := ⟨v i, orthogonal_of_no_eigenvector hT K hK (hb i) (hn i)⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp (Kᗮ).subtype hv
  have h := hw.fintype_card_le_finrank
  have := K.finrank_add_finrank_orthogonal
  omega

private theorem trace_pow_eq_sum_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow, Matrix.diagonal_pow,
    Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal]


open MathlibExt.Probability.RandomTranspositionEstimates

-- Choose the *largest* deficit compatible with the eigenvalue. This makes the assignment
-- independent of any choice of eigenvectors inside repeated eigenspaces.
private noncomputable def level (n : ℕ) (b : ℝ) : ℕ :=
  Nat.findGreatest (fun j => b ≤ cap n j) n

private theorem eigen_cap {n : ℕ} [NeZero n] {f : G n → ℝ} {b : ℝ} (hf : f ≠ 0)
    (he : A n *ᵥ f = b • f) :
    ∃ R : Finset (Fin n), symSum R f ≠ 0 ∧ b ≤ cap n (n - R.card) := by
  have he' : transSum Finset.univ f = ((n : ℝ) ^ 2 * b) • f := by
    rw [transSum_eq, he, smul_smul]
  obtain ⟨R, _, hg, h1, h2⟩ := exists_level_bounds_univ hf he'
  simp only [Fintype.card_fin] at h1 h2
  have hR : R.card ≤ n := by simpa using R.card_le_univ
  have hn : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  refine ⟨R, hg, ?_⟩
  unfold cap
  push_cast [Nat.cast_sub hR]
  apply le_min
  · rw [le_sub_comm, div_le_iff₀ (sq_pos_of_pos hn)]
    nlinarith
  · rw [le_sub_comm, div_le_iff₀ hn]
    apply le_of_mul_le_mul_left (a := (n : ℝ)) _ hn
    nlinarith

private theorem level_bound {n : ℕ} [NeZero n] {f : G n → ℝ} {b : ℝ} (hf : f ≠ 0)
    (he : A n *ᵥ f = b • f) : b ≤ cap n (level n b) := by
  obtain ⟨R, _, hb⟩ := eigen_cap hf he
  exact Nat.findGreatest_spec (P := fun j => b ≤ cap n j) (Nat.sub_le _ _) hb

-- The eigenvectors at a given assigned level lie orthogonal to the simultaneous kernel
-- of the corresponding symmetrisers. Count them using the rank of the restriction map.
private theorem level_card {n j : ℕ} [NeZero n] (hj : j ≤ n) {ι : Type*} [Fintype ι]
    (v : ι → (G n → ℝ)) (hv : LinearIndependent ℝ v) (b : ι → ℝ)
    (he : ∀ i, A n *ᵥ v i = b i • v i) (hl : ∀ i, level n (b i) = j) :
    Fintype.card ι ≤ n.choose j * n ^ j := by
  let e := WithLp.linearEquiv 2 ℝ (G n → ℝ)
  let L := (symRankMap (n := n) j).comp e.toLinearMap
  let T := (A n).toEuclideanLin
  have hTe (w : EuclideanSpace ℝ (G n)) : e (T w) = A n *ᵥ e w := rfl
  have hK (w) (hw : w ∈ L.ker) : T w ∈ L.ker := by
    change e (T w) ∈ (symRankMap j).ker
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    rw [hTe, ← (symRankMap j).ker.smul_mem_iff (pow_ne_zero 2 hn), ← transSum_eq]
    exact transSum_mem_ker_symRankMap hj hw
  have hne (i : ι) (w : EuclideanSpace ℝ (G n)) (hw : w ∈ L.ker) (hew : T w = b i • w) :
      w = 0 := by
    by_contra hw0
    have hew' : A n *ᵥ e w = b i • e w := by rw [← hTe, hew, map_smul]
    obtain ⟨R, hR, hc⟩ := eigen_cap (by simpa using hw0 : e w ≠ 0) hew'
    have hle := Nat.le_findGreatest (P := fun l => b i ≤ cap n l) (Nat.sub_le n R.card) hc
    change n - R.card ≤ level n (b i) at hle
    rw [hl i] at hle
    have hz := (mem_ker_symRankMap_iff_ge hj _).mp (show e w ∈ (symRankMap j).ker from hw)
    exact hR (hz R (by omega))
  have hi := card_eigenvectors_le_codim (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hermitian n))
    L.ker hK (fun i => e.symm (v i))
    (hv.map' _ (LinearMap.ker_eq_bot_of_injective e.symm.injective)) b
    (fun i => e.injective (by rw [hTe, map_smul, e.apply_symm_apply, he])) hne
  have hdim := L.finrank_range_add_finrank_ker
  have hr : finrank ℝ L.range ≤ n.choose j * n ^ j := L.range.finrank_le.trans_eq
    ((Module.finrank_fintype_fun_eq_card ℝ).trans (card_symRankCoord n j))
  apply le_trans _ hr
  exact Nat.le_of_add_le_add_right (show Fintype.card ι + finrank ℝ L.ker ≤
    finrank ℝ L.range + finrank ℝ L.ker by rw [hdim]; exact hi)

private theorem cutoff (n k : ℕ) [NeZero n] (hn : 2 ≤ n) :
    2 * tvDist (convPow (randomTransposition n) k) (uniform (G n)) ≤
      (2 * Real.exp 3) * (n * Real.exp (-2 * (k : ℝ) / n)) := by
  classical
  let H := hermitian n
  let u := H.eigenvalues
  let v : G n → G n → ℝ := fun i => (H.eigenvectorBasis i).ofLp
  let e := WithLp.linearEquiv 2 ℝ (G n → ℝ)
  have hv : LinearIndependent ℝ v := H.eigenvectorBasis.toBasis.linearIndependent.map'
    e.toLinearMap (LinearMap.ker_eq_bot_of_injective e.injective)
  have he (i) : A n *ᵥ v i = u i • v i := H.mulVec_eigenvectorBasis i
  have ht : LinearIndependent ℝ (fun i => signMap n (v i)) := hv.map' (signMap n)
    (LinearMap.ker_eq_bot_of_injective (signMap_inj n))
  let d (i : G n) := level n (oriented n (u i))
  apply cutoff_of_spectrum (k := k) hn u d (fun _ => Nat.findGreatest_le _)
  · intro i
    by_cases hi : 0 ≤ u i
    · simpa [d, oriented, hi] using level_bound (hv.ne_zero i) (he i)
    · simpa [d, oriented, hi] using level_bound (ht.ne_zero i) (twist_eigen (he i))
  · intro j hj
    let s := Finset.univ.filter (fun i => 0 ≤ u i ∧ d i = j)
    rw [← Fintype.card_coe (s := s)]
    refine level_card hj (v ∘ ((↑) : s → G n)) (hv.comp _ Subtype.val_injective)
      (u ∘ ((↑) : s → G n)) (fun i => he i) ?_
    intro i
    obtain ⟨hi, hd⟩ := (Finset.mem_filter.mp i.2).2
    simpa [d, oriented, hi] using hd
  · intro j hj
    let s := Finset.univ.filter (fun i => u i < 0 ∧ d i = j)
    rw [← Fintype.card_coe (s := s)]
    refine level_card hj (fun i : s => signMap n (v i)) (ht.comp _ Subtype.val_injective)
      (fun i : s => 2 / n - u i) (fun i => twist_eigen (he i)) ?_
    intro i
    obtain ⟨hi, hd⟩ := (Finset.mem_filter.mp i.2).2
    simpa [d, oriented, not_le.mpr hi] using hd
  · exact tvBound n k
  · have h := four_mul_tvDist_sq_le_trace_walkMatrix_pow (randomTransposition n)
      (sum_randomTransposition n) (randomTransposition_inv n) k
    rw [trace_pow_eq_sum_pow H] at h
    linarith only [h]

end MathlibExt.Probability.RandomTranspositionUpper

namespace MathlibExt.Probability.RandomWalkFiniteGroupWanted

/-- **Random transpositions: `(1/2) n log n + c n` steps suffice (Diaconis–Shahshahani).** There
is a constant `b > 0` such that for all `n ≥ 10` and all `k` with
`c = (k - (1/2) n log n) / n > 0`, the law `T^{*k}` of `k` random transpositions satisfies
`‖T^{*k} - U‖ ≤ b e^{-2c}` in the `ℓ¹` norm `‖·‖ = 2 ‖·‖_TV` (Diaconis and Shahshahani 1981,
Theorem 1 with (1.1)–(1.4); the constant is universal, Section 3 and Remark 1 of Section 5 compute
it explicitly). -/
public theorem diaconis_shahshahani_upper :
    ∃ b : ℝ, 0 < b ∧ ∀ (n k : ℕ) [NeZero n], 10 ≤ n →
      0 < ((k : ℝ) - n * Real.log n / 2) / n →
      2 * tvDist (convPow (randomTransposition n) k) (uniform (Equiv.Perm (Fin n))) ≤
        b * Real.exp (-2 * (((k : ℝ) - n * Real.log n / 2) / n)) := by
  refine ⟨2 * Real.exp 3, by positivity, ?_⟩
  intro n k _ hn _
  rw [← MathlibExt.Probability.RandomTranspositionEstimates.cutoff_rate_eq (NeZero.pos n)]
  exact MathlibExt.Probability.RandomTranspositionUpper.cutoff n k (by omega)

end MathlibExt.Probability.RandomWalkFiniteGroupWanted
