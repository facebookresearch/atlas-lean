/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Dvoretzky–Rogers theorem

Every infinite-dimensional real Banach space has an unconditionally summable series whose
series of norms diverges. The proof constructs finite blocks with small subset sums via
Hahn–Banach separation, then assembles the blocks using a geometric bound.
-/

open Set

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook122Wanted

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem sum_norm_le_subset_of_no_block {ε : ℝ} (hε : 0 < ε)
    (h : ∀ (n : ℕ) (x : Fin n → E),
      (∀ s : Finset (Fin n), ‖∑ i ∈ s, x i‖ ≤ ε) → ∑ i, ‖x i‖ < 1)
    {n : ℕ} (x : Fin n → E) :
    ∃ s : Finset (Fin n), ∑ i, ‖x i‖ ≤ ε⁻¹ * ‖∑ i ∈ s, x i‖ := by
  classical
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ
    (fun t : Finset (Fin n) => ‖∑ i ∈ t, x i‖) Finset.univ_nonempty
  let M := ‖∑ i ∈ s, x i‖
  have hM (t : Finset (Fin n)) : ‖∑ i ∈ t, x i‖ ≤ M := hs t (Finset.mem_univ _)
  refine ⟨s, ?_⟩
  by_cases hM₀ : M = 0
  · have hz (i : Fin n) : ‖x i‖ = 0 :=
      le_antisymm (by simpa [hM₀] using hM {i}) (norm_nonneg _)
    simp [hz, ← show M = ‖∑ i ∈ s, x i‖ from rfl, hM₀]
  have hMpos : 0 < M := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hM₀)
  have hscale : 0 ≤ ε / M := by positivity
  have hb := h n (fun i => (ε / M) • x i) fun t => by
    rw [← Finset.smul_sum, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
    calc
      (ε / M) * ‖∑ i ∈ t, x i‖ ≤ (ε / M) * M := mul_le_mul_of_nonneg_left (hM t) hscale
      _ = ε := div_mul_cancel₀ _ hM₀
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, ← Finset.mul_sum] at hb
  change ∑ i, ‖x i‖ ≤ ε⁻¹ * M
  rw [inv_mul_eq_div, le_div_iff₀ hε]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hMpos, one_mul, mul_comm] at hb
  exact hb.le

private theorem sum_sq_le_dual {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (n : ℕ) (x : Fin n → E),
      ∃ s : Finset (Fin n), ∑ i, ‖x i‖ ≤ C * ‖∑ i ∈ s, x i‖)
    {n : ℕ} (x : Fin n → E) :
    ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧ ∑ i, ‖x i‖ ^ 2 ≤ C ^ 2 * ∑ i, (f (x i)) ^ 2 := by
  classical
  let y (i : Fin n) := ‖x i‖ • x i
  obtain ⟨s, hs⟩ := h n y
  obtain ⟨f, hf, hfₛ⟩ := exists_dual_vector'' ℝ (∑ i ∈ s, y i)
  change f (∑ i ∈ s, y i) = ‖∑ i ∈ s, y i‖ at hfₛ
  refine ⟨f, hf, ?_⟩
  let A := ∑ i, ‖x i‖ ^ 2
  let B := ∑ i, ‖x i‖ * |f (x i)|
  let D := ∑ i, (f (x i)) ^ 2
  have hAB : A ≤ C * B := calc
    A = ∑ i, ‖y i‖ := by simp [A, y, norm_smul, pow_two]
    _ ≤ C * ‖∑ i ∈ s, y i‖ := hs
    _ ≤ C * B := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [← hfₛ, map_sum]
      calc
        (∑ i ∈ s, f (y i)) ≤ ∑ i ∈ s, |f (y i)| :=
          Finset.sum_le_sum fun _ _ => le_abs_self _
        _ = ∑ i ∈ s, ‖x i‖ * |f (x i)| := by
          simp [y, map_smul, smul_eq_mul, abs_mul, abs_of_nonneg]
        _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _))
  have hAD : B ^ 2 ≤ A * D := by
    simpa only [A, B, D, sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖x i‖) (fun i => |f (x i)|)
  change A ≤ C ^ 2 * D
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg ‖x i‖
  rcases hA.eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg (sq_nonneg C) (Finset.sum_nonneg fun i _ => sq_nonneg (f (x i)))
  apply le_of_mul_le_mul_left _ hpos
  calc
    A * A = A ^ 2 := by ring
    _ ≤ (C * B) ^ 2 := pow_le_pow_left₀ hA hAB 2
    _ = C ^ 2 * B ^ 2 := by ring
    _ ≤ C ^ 2 * (A * D) := mul_le_mul_of_nonneg_left hAD (sq_nonneg C)
    _ = A * (C ^ 2 * D) := by ring

-- Only the left linearity equations are needed because the forms are symmetric.
private def symmForms (E : Type*) [AddCommGroup E] [Module ℝ E] :
    Submodule ℝ (E × E → ℝ) where
  carrier := {q | (∀ x y, q (y, x) = q (x, y)) ∧
    (∀ x y z, q (x + y, z) = q (x, z) + q (y, z)) ∧
    (∀ x y (a : ℝ), q (a • x, y) = a * q (x, y))}
  zero_mem' := by simp
  add_mem' := by
    rintro q r ⟨hq₁, hq₂, hq₃⟩ ⟨hr₁, hr₂, hr₃⟩
    refine ⟨fun x y => ?_, fun x y z => ?_, fun x y a => ?_⟩
    · simp [Pi.add_apply, hq₁ x y, hr₁ x y]
    · simp only [Pi.add_apply, hq₂, hr₂]
      ring
    · simp only [Pi.add_apply, hq₃, hr₃]
      ring
  smul_mem' := by
    rintro a q ⟨hq₁, hq₂, hq₃⟩
    refine ⟨fun x y => ?_, fun x y z => ?_, fun x y b => ?_⟩
    · simp [Pi.smul_apply, hq₁ x y]
    · simp only [Pi.smul_apply, smul_eq_mul, hq₂]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul, hq₃]
      ring

private theorem symmForms_isClosed : IsClosed (symmForms E : Set (E × E → ℝ)) := by
  change IsClosed {q : E × E → ℝ | (∀ x y, q (y, x) = q (x, y)) ∧
    (∀ x y z, q (x + y, z) = q (x, z) + q (y, z)) ∧
    (∀ x y (a : ℝ), q (a • x, y) = a * q (x, y))}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq (continuous_apply (y, x)) (continuous_apply (x, y))).inter
    ((isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_eq (continuous_apply (x + y, z))
        ((continuous_apply (x, z)).add (continuous_apply (y, z)))).inter
    (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun a =>
      isClosed_eq (continuous_apply (a • x, y)) (continuous_const.mul (continuous_apply (x, y)))))

private theorem exists_dominating_form {C : ℝ} (hC : 0 < C)
    (h : ∀ (n : ℕ) (x : Fin n → E),
      ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧ ∑ i, ‖x i‖ ^ 2 ≤ C ^ 2 * ∑ i, (f (x i)) ^ 2) :
    ∃ q ∈ symmForms E, ∀ x, ‖x‖ ^ 2 / C ^ 2 ≤ q (x, x) ∧ q (x, x) ≤ ‖x‖ ^ 2 := by
  classical
  let K : Set (E × E → ℝ) := (Set.univ.pi fun p : E × E =>
    Set.Icc (-(‖p.1‖ * ‖p.2‖)) (‖p.1‖ * ‖p.2‖)) ∩ symmForms E
  have hK : IsCompact K := (isCompact_univ_pi fun _ => isCompact_Icc).inter_right symmForms_isClosed
  have hKc : Convex ℝ K :=
    (convex_pi fun _ _ => convex_Icc _ _).inter (symmForms E).convex
  have hdual (f : StrongDual ℝ E) (hf : ‖f‖ ≤ 1) :
      (fun p : E × E => f p.1 * f p.2) ∈ K := by
    refine ⟨Set.mem_univ_pi.mpr (fun p => ?_), ?_⟩
    · have hb (x : E) : |f x| ≤ ‖x‖ := by
        rw [← Real.norm_eq_abs]
        exact (f.le_opNorm x).trans (by
          simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg x))
      change -(‖p.1‖ * ‖p.2‖) ≤ f p.1 * f p.2 ∧ f p.1 * f p.2 ≤ ‖p.1‖ * ‖p.2‖
      apply abs_le.mp
      rw [abs_mul]
      exact mul_le_mul (hb p.1) (hb p.2) (abs_nonneg _) (norm_nonneg _)
    · change (∀ x y, f y * f x = f x * f y) ∧
        (∀ x y z, f (x + y) * f z = f x * f z + f y * f z) ∧
        (∀ x y (a : ℝ), f (a • x) * f y = a * (f x * f y))
      exact ⟨fun _ _ => mul_comm .., by simp [add_mul], by simp [mul_assoc]⟩
  let T (x : E) : Set (E × E → ℝ) := {q | ‖x‖ ^ 2 / C ^ 2 ≤ q (x, x)}
  -- Separate the diagonal evaluations from their coordinatewise lower bounds.
  have hfin (n : ℕ) (x : Fin n → E) : (K ∩ ⋂ i, T (x i)).Nonempty := by
    let P : (E × E → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun i => LinearMap.proj (x i, x i)
    let r (i : Fin n) := ‖x i‖ ^ 2 / C ^ 2
    by_contra hempty
    have hdisj : Disjoint (P '' K) (Ici r) := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨q, hq, rfl⟩ hqr
      exact hempty ⟨q, hq, Set.mem_iInter.mpr hqr⟩
    obtain ⟨L, u, v, hLu, huv, hLv⟩ := geometric_hahn_banach_compact_closed
      (hKc.linear_image P) (hK.image (continuous_pi fun i => continuous_apply (x i, x i)))
      (convex_Ici r) isClosed_Ici hdisj
    -- A separating functional must be nonnegative on each positive coordinate ray.
    let w (i : Fin n) := L (Pi.single i 1)
    have hw (i : Fin n) : 0 ≤ w i := by
      by_contra! hn
      obtain ⟨m, hm⟩ := exists_nat_gt ((L r - v) / (-w i))
      have ht : r + (m : ℝ) • Pi.single i 1 ∈ Ici r := by
        intro j
        change r j ≤ r j + (m : ℝ) * Pi.single (M := fun _ => ℝ) i 1 j
        apply le_add_of_nonneg_right
        by_cases hj : j = i
        · subst j
          simp
        · simp [Pi.single_eq_of_ne hj]
      have hl := hLv _ ht
      rw [map_add, map_smul, smul_eq_mul] at hl
      rw [div_lt_iff₀ (by linarith)] at hm
      dsimp [w] at hm
      linarith
    have hL (z : Fin n → ℝ) : L z = ∑ i, w i * z i := by
      have hz : (∑ i : Fin n, z i • Pi.single i (1 : ℝ)) = z := by
        ext i
        rw [Finset.sum_apply, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Pi.single_eq_of_ne hji.symm]
        · simp
      calc
        L z = L (∑ i : Fin n, z i • Pi.single i (1 : ℝ)) := congrArg L hz.symm
        _ = ∑ i, w i * z i := by
          rw [map_sum]
          simp only [map_smul, smul_eq_mul, w, mul_comm]
    obtain ⟨f, hf, hfx⟩ := h n (fun i => Real.sqrt (w i) • x i)
    have hdom : ∑ i, w i * r i ≤ ∑ i, w i * (f (x i)) ^ 2 := by
      have hsqrt (i : Fin n) : (Real.sqrt (w i)) ^ 2 = w i := Real.sq_sqrt (hw i)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), map_smul,
        smul_eq_mul, mul_pow, hsqrt] at hfx
      calc
        (∑ i, w i * r i) = (∑ i, w i * ‖x i‖ ^ 2) / C ^ 2 := by
          simp only [r, Finset.sum_div, mul_div_assoc]
        _ ≤ ∑ i, w i * (f (x i)) ^ 2 :=
          (div_le_iff₀ (pow_pos hC 2)).2 (by simpa only [mul_comm] using hfx)
    have hlt := hLu _ ⟨_, hdual f hf, rfl⟩
    have hrt := hLv r (mem_Ici.mpr le_rfl)
    rw [hL] at hlt hrt
    change (∑ i, w i * (f (x i) * f (x i))) < u at hlt
    simp only [← pow_two] at hlt
    linarith
  -- Compactness turns feasibility on finite sets into simultaneous domination.
  obtain ⟨q, hq, hT⟩ := hK.inter_iInter_nonempty T
    (fun x => isClosed_le continuous_const (continuous_apply (x, x))) (fun s => by
      let e := s.equivFin
      obtain ⟨q, hqK, hqT⟩ := hfin s.card (fun i => (e.symm i : E))
      refine ⟨q, hqK, Set.mem_iInter.mpr fun x => Set.mem_iInter.mpr fun hx => ?_⟩
      simpa using Set.mem_iInter.mp hqT (e ⟨x, hx⟩))
  exact ⟨q, hq.2, fun x => ⟨Set.mem_iInter.mp hT x,
    by simpa [pow_two] using (Set.mem_univ_pi.mp hq.1 (x, x)).2⟩⟩

end

private theorem not_sum_norm_le_subset
    {E : Type*} [AddCommGroup E] [Module ℝ E] (hinf : ¬ Module.Finite ℝ E)
    (p : E → ℝ) (hp : ∀ x, 0 ≤ p x) (hp₀ : ∀ x, p x = 0 → x = 0)
    {C : ℝ} (hC : 0 < C) {q : E × E → ℝ} (hq : q ∈ symmForms E)
    (hdiag : ∀ x, p x ^ 2 / C ^ 2 ≤ q (x, x) ∧ q (x, x) ≤ p x ^ 2)
    (h : ∀ (n : ℕ) (x : Fin n → E),
      ∃ s : Finset (Fin n), ∑ i, p (x i) ≤ C * p (∑ i ∈ s, x i)) : False := by
  obtain ⟨hsymm, hadd, hsmul⟩ := hq
  have hnonneg (x : E) : 0 ≤ q (x, x) := (by positivity : 0 ≤ p x ^ 2 / C ^ 2).trans (hdiag x).1
  let core : InnerProductSpace.Core ℝ E :=
    { inner := fun x y => q (x, y)
      conj_inner_symm := fun x y => by simpa using hsymm x y
      re_inner_nonneg := fun x => by simpa using hnonneg x
      add_left := hadd
      smul_left := fun x y a => by simpa using hsmul x y a
      definite := fun x hx => hp₀ x (le_antisymm
        (le_of_sq_le_sq (by
          have hx' := (hdiag x).1
          rw [hx, div_le_iff₀ (by positivity)] at hx'
          simpa using hx') le_rfl) (hp x)) }
  let : NormedAddCommGroup E := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ E := InnerProductSpace.ofCore core.toCore
  -- Here the norm notation refers to the inner product, and p is the original norm.
  have hnorm (x : E) : ‖x‖ ^ 2 = q (x, x) := by
    change (Real.sqrt (q (x, x))) ^ 2 = q (x, x)
    exact Real.sq_sqrt (hnonneg x)
  have hlower (x : E) : ‖x‖ ≤ p x :=
    le_of_sq_le_sq ((hnorm x).trans_le (hdiag x).2) (hp x)
  have hupper (x : E) : p x ≤ C * ‖x‖ := by
    apply le_of_sq_le_sq _ (mul_nonneg hC.le (norm_nonneg _))
    rw [mul_pow, hnorm, mul_comm]
    exact (div_le_iff₀ (by positivity)).mp (hdiag x).1
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 4)
  have hrank : Cardinal.aleph0 ≤ Module.rank ℝ E :=
    le_of_not_gt (mt Module.rank_lt_aleph0_iff.mp hinf)
  obtain ⟨y, hy⟩ := exists_linearIndependent_of_le_rank
    (Cardinal.natCast_lt_aleph0.le.trans hrank : (n : Cardinal) ≤ Module.rank ℝ E)
  let x := InnerProductSpace.gramSchmidtNormed ℝ y
  have hx : Orthonormal ℝ x := InnerProductSpace.gramSchmidtNormed_orthonormal hy
  obtain ⟨s, hs⟩ := h n x
  have hn₁ : (n : ℝ) ≤ ∑ i, p (x i) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hx.norm_eq_one i).symm.le.trans
      (hlower (x i)))
  have hn₂ : ‖∑ i ∈ s, x i‖ ≤ Real.sqrt n := by
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (Nat.cast_nonneg n), norm_sq_eq_re_inner (𝕜 := ℝ), RCLike.re_to_real]
    have hsum := hx.inner_sum (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) s
    simp only [one_smul, map_one, mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    rw [hsum]
    exact_mod_cast (by simpa using s.card_le_univ : s.card ≤ n)
  have hbound : (n : ℝ) ≤ C ^ 2 * Real.sqrt n := calc
    (n : ℝ) ≤ ∑ i, p (x i) := hn₁
    _ ≤ C * p (∑ i ∈ s, x i) := hs
    _ ≤ C * (C * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left ((hupper _).trans (mul_le_mul_of_nonneg_left hn₂ hC.le)) hC.le
    _ = C ^ 2 * Real.sqrt n := by ring
  have hlt : C ^ 2 < Real.sqrt n := (Real.lt_sqrt (sq_nonneg C)).2 (by
    rwa [← pow_mul])
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),
    mul_lt_mul_of_pos_right hlt (lt_of_le_of_lt (sq_nonneg C) hlt)]

private theorem exists_block {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hinf : ¬ Module.Finite ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (x : Fin n → E), 1 ≤ ∑ i, ‖x i‖ ∧
      ∀ s : Finset (Fin n), ‖∑ i ∈ s, x i‖ ≤ ε := by
  by_contra h
  have hC := inv_pos.mpr hε
  have hsubset := fun (n : ℕ) (x : Fin n → E) =>
    sum_norm_le_subset_of_no_block hε (fun m y hy =>
      lt_of_not_ge fun hb => h ⟨m, y, hb, hy⟩) x
  obtain ⟨q, hq, hdiag⟩ := exists_dominating_form hC (fun _ => sum_sq_le_dual hC.le hsubset)
  exact not_sum_norm_le_subset hinf (fun x => ‖x‖) norm_nonneg
    (fun _ => norm_eq_zero.mp) hC hq hdiag hsubset

@[expose] public section

/--
**Dvoretzky–Rogers theorem.** Every infinite-dimensional real Banach space $E$ contains a series
that converges unconditionally but not absolutely: there is a sequence $(x_n)_{n \ge 0}$ in $E$
such that the rearranged series $\sum_n x_{\sigma(n)}$ converges for every permutation $\sigma$
of $\mathbb{N}$, while $\sum_n \lVert x_n \rVert$ diverges.

Source: S. Mazur and W. Orlicz,
Problem 122 of the Scottish Book; A. Dvoretzky and C. A. Rogers, "Absolute
and unconditional convergence in normed linear spaces", Proc. Natl. Acad.
Sci. USA 36 (1950), 192-197.
-/
theorem dvoretzky_rogers_unconditional_not_absolute :
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      ¬ Module.Finite ℝ E →
      ∃ x : ℕ → E,
        (∀ σ : Equiv.Perm ℕ, Summable (x ∘ σ)) ∧
        ¬ Summable (fun n => ‖x n‖) := by
  intro E _ _ _ hinf
  classical
  let r (k : ℕ) : ℝ := (1 / 2) ^ k
  have hr : Summable r := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hb (k : ℕ) := exists_block hinf (ε := r k) (by dsimp [r]; positivity)
  choose n y hmass hblock using hb
  let z (a : Σ k : ℕ, Fin (n k)) := y a.1 a.2
  -- Group each finite tail by blocks and compare it with a geometric tail.
  have hz : Summable z := by
    refine summable_iff_vanishing_norm.2 fun ε hε => ?_
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hr ε hε
    refine ⟨s.sigma (fun _ => Finset.univ), fun t ht => ?_⟩
    have hdisj : Disjoint (t.image Sigma.fst) s := by
      refine Finset.disjoint_left.mpr ?_
      intro k hk hks
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.disjoint_left.mp ht ha (Finset.mem_sigma.mpr ⟨hks, Finset.mem_univ _⟩)
    let fiber (k : ℕ) := t.preimage (Sigma.mk k) sigma_mk_injective.injOn
    calc
      ‖∑ a ∈ t, z a‖ = ‖∑ k ∈ t.image Sigma.fst, ∑ i ∈ fiber k, y k i‖ := by
        rw [Finset.sum_sigma', Finset.sigma_image_fst_preimage_mk]
      _ ≤ ∑ k ∈ t.image Sigma.fst, r k :=
        norm_sum_le_of_le _ (fun k _ => hblock k (fiber k))
      _ ≤ ‖∑ k ∈ t.image Sigma.fst, r k‖ := le_abs_self _
      _ < ε := hs _ hdisj
  have hnorm : ¬ Summable (fun a => ‖z a‖) := by
    intro habs
    have hsum := (summable_sigma_of_nonneg (fun a => norm_nonneg (z a))).mp habs
    have hone : Summable (fun _ : ℕ => (1 : ℝ)) :=
      Summable.of_nonneg_of_le (fun _ => zero_le_one)
        (fun k => by simpa [z, tsum_fintype] using hmass k) hsum.2
    exact one_ne_zero ((summable_const_iff 1).mp hone)
  have hpos (k : ℕ) : 0 < n k := by
    by_contra! hzero
    have hn := hmass k
    have : IsEmpty (Fin (n k)) :=
      ⟨fun i => (not_lt_of_ge hzero) ((Nat.zero_le i.val).trans_lt i.isLt)⟩
    exact not_le_of_gt zero_lt_one (by simpa using hn)
  have : Infinite (Σ k : ℕ, Fin (n k)) :=
    Infinite.of_injective (fun k : ℕ => (⟨k, 0, hpos k⟩ : Σ k : ℕ, Fin (n k)))
      (fun _ _ h => congrArg Sigma.fst h)
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := Σ k : ℕ, Fin (n k))
  refine ⟨z ∘ e, fun σ => σ.summable_iff.mpr (e.summable_iff.mpr hz), ?_⟩
  exact fun h => hnorm (e.summable_iff.mp h)

end

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook122Wanted
