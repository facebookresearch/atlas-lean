/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Dynamics/MoranDimension.lean` (leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e).
Copyright 2026 Lean FRO, LLC.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Kim Morrison (problem submitter).

The adapted portions are the three definitions and the statement of Moran's equality.
They were namespaced and documented in `WantedExt/Dynamics/MoranDimensionWanted.lean`.
The proof is original to ATLAS. lean-eval ships no `NOTICE` file.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn

/-!
# Moran's equality for affine-symmetric iterated function systems

`moran_equality_affine` computes the Hausdorff dimension of a compact attractor for similarities
with a common contraction factor satisfying the open set condition. Level covers give the upper
bound. For the lower bound, a coding by infinite words carries the uniform Bernoulli mass to
the attractor, and the open set condition bounds the number of pieces meeting a ball at each scale.
-/

@[expose] public section

namespace MathlibExt.Dynamics.MoranDimensionWanted.Dynamics

open Set Metric MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology

set_option linter.dupNamespace false in
/-- **Attractor of an iterated function system.** Let $X$ be a topological space and let
$(f_i)_{i < n}$ be a finite family of maps $X \to X$. A set $S \subseteq X$ is an attractor of the
family if it is nonempty and compact and is fixed by the Hutchinson operator, that is,
$S = \bigcup_{i < n} f_i(S)$. -/
def IsAttractor {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : Fin n → X → X) (S : Set X) : Prop :=
  IsCompact S ∧ S.Nonempty ∧ S = ⋃ i, f i '' S

set_option linter.dupNamespace false in
/-- **Affine-symmetric iterated function system.** Let $(f_i)_{i < n}$ be a finite family of maps
$f_i \colon \mathbb{R}^d \to \mathbb{R}^d$ on Euclidean space. The family is affine-symmetric with
common contraction factor $\lambda$ if $0 < \lambda < 1$ and there are linear isometries
$A_i \colon \mathbb{R}^d \to \mathbb{R}^d$ (orthogonal transformations) and vectors
$\beta_i \in \mathbb{R}^d$ such that $f_i(x) = \lambda A_i(x) + \beta_i$ for every $i < n$ and every
$x \in \mathbb{R}^d$. -/
def IsAffineSymmetricIFS {d n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    Prop :=
  0 < lam ∧ lam < 1 ∧
  ∃ A : Fin n → (EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)),
    ∃ β : Fin n → EuclideanSpace ℝ (Fin d),
      ∀ i x, f i x = lam • A i x + β i

set_option linter.dupNamespace false in
/-- **Open set condition.** A finite family of maps $f_i \colon \mathbb{R}^d \to \mathbb{R}^d$,
$i < n$, satisfies the open set condition if there is a nonempty open set $G \subseteq \mathbb{R}^d$
such that $f_i(G) \subseteq G$ for every $i < n$ and the images $f_i(G)$ and $f_j(G)$ are disjoint
whenever $i \neq j$. -/
def OpenSetCondition {d n : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ G : Set (EuclideanSpace ℝ (Fin d)), IsOpen G ∧ G.Nonempty ∧
    (∀ i, f i '' G ⊆ G) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (f i '' G) (f j '' G))

local notation "Space" d:arg => EuclideanSpace ℝ (Fin d)

variable {d n : ℕ} {f : Fin n → Space d → Space d} {lam : ℝ} {S G : Set (Space d)}

private def word (f : Fin n → Space d → Space d) : {k : ℕ} → (Fin k → Fin n) → Space d → Space d
  | 0, _ => id
  | k + 1, w => word f (Fin.init w) ∘ f (w (Fin.last k))

private lemma word_dist (hf : ∀ i x y, dist (f i x) (f i y) = lam * dist x y)
    {k : ℕ} (w : Fin k → Fin n) (x y : Space d) :
    dist (word f w x) (word f w y) = lam ^ k * dist x y := by
  induction k generalizing x y with
  | zero => simp [word]
  | succ k ih => simp [word, ih, hf, pow_succ, mul_assoc]

private lemma word_surj (hf : ∀ i, Function.Surjective (f i))
    {k : ℕ} (w : Fin k → Fin n) : Function.Surjective (word f w) := by
  induction k with
  | zero => exact Function.surjective_id
  | succ k ih => exact (ih _).comp (hf _)

private lemma word_cover (hS : IsAttractor f S) (k : ℕ) :
    S ⊆ ⋃ w : Fin k → Fin n, word f w '' S := by
  induction k with
  | zero => exact fun x hx => mem_iUnion.mpr ⟨Fin.elim0, x, hx, rfl⟩
  | succ k ih =>
    intro x hx
    obtain ⟨w, y, hy, rfl⟩ := mem_iUnion.mp (ih hx)
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp (hS.2.2.le hy)
    exact mem_iUnion.mpr ⟨Fin.snoc w i, z, hz, by simp [word]⟩

private lemma word_lipschitz (hl : 0 < lam)
    (hf : ∀ i x y, dist (f i x) (f i y) = lam * dist x y) {k : ℕ} (w : Fin k → Fin n) :
    LipschitzWith (lam.toNNReal ^ k) (word f w) := by
  apply LipschitzWith.of_dist_le_mul
  simp [word_dist hf, Real.toNNReal_of_nonneg hl.le]

private lemma word_disjoint (hl : 0 < lam)
    (hf : ∀ i x y, dist (f i x) (f i y) = lam * dist x y)
    (hin : ∀ i, f i '' G ⊆ G) (hdis : Pairwise fun i j => Disjoint (f i '' G) (f j '' G))
    (k : ℕ) : Pairwise fun w v : Fin k → Fin n => Disjoint (word f w '' G) (word f v '' G) := by
  induction k with
  | zero => exact fun w v h => (h (Subsingleton.elim w v)).elim
  | succ k ih =>
    intro w v h
    simp only [word, image_comp]
    by_cases he : Fin.init w = Fin.init v
    · rw [he]
      have hlast : w (Fin.last k) ≠ v (Fin.last k) := by
        intro hz
        apply h
        rw [← Fin.snoc_init_self w, he, hz, Fin.snoc_init_self]
      refine disjoint_image_of_injective ?_ (hdis hlast)
      intro x y hxy
      have hzero := word_dist hf (Fin.init v) x y
      rw [hxy, dist_self] at hzero
      exact dist_eq_zero.mp ((mul_eq_zero.mp hzero.symm).resolve_left (pow_ne_zero _ hl.ne'))
    · exact (ih he).mono (image_mono (hin _)) (image_mono (hin _))

private lemma exists_code (hl : 0 < lam)
    (hf : ∀ i x y, dist (f i x) (f i y) = lam * dist x y) (hS : IsAttractor f S) :
    ∃ code : (ℕ → Fin n) → Space d, ∀ a k, code a ∈ word f (fun i : Fin k => a i) '' S := by
  classical
  suffices h : ∀ a : ℕ → Fin n, (⋂ k, word f (fun i : Fin k => a i) '' S).Nonempty by
    exact ⟨fun a => (h a).choose, fun a => mem_iInter.mp (h a).choose_spec⟩
  intro a
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro k
    change (word f _ ∘ _) '' S ⊆ _
    rw [image_comp]
    apply image_mono
    exact (subset_iUnion (fun i => f i '' S) _).trans hS.2.2.ge
  · exact fun k => hS.2.1.image _
  · simpa [word] using hS.1
  · exact fun k => (hS.1.image (word_lipschitz hl hf _).continuous).isClosed

private lemma upper_bound (hn : n ≠ 0) (hl : 0 < lam) (h1 : lam < 1)
    (hf : ∀ i x y, dist (f i x) (f i y) = lam * dist x y) (hS : IsAttractor f S)
    (s : ℝ≥0) (hs : ENNReal.ofReal lam ^ (s : ℝ) = (n : ℝ≥0∞)⁻¹) :
    dimH S ≤ s := by
  let c := ENNReal.ofReal lam
  have hD := hS.1.isBounded.ediam_ne_top
  have hc : c < 1 := (ENNReal.ofReal_lt_one).2 h1
  have hlim : Tendsto (fun k : ℕ => c ^ k * ediam S) atTop (𝓝 0) := by
    simpa using (ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc)
      (Or.inr hD))
  have hdiam (k : ℕ) (w : Fin k → Fin n) : ediam (word f w '' S) ≤ c ^ k * ediam S := by
    simpa [c, ENNReal.ofReal] using (word_lipschitz hl hf w).ediam_image_le S
  apply dimH_le_of_hausdorffMeasure_ne_top
  apply ne_top_of_le_ne_top (b := ediam S ^ (s : ℝ))
    (ENNReal.rpow_ne_top_of_nonneg s.2 hD)
  refine (hausdorffMeasure_le_liminf_sum (s : ℝ) S _ hlim
    (fun k w => word f w '' S) (.of_forall hdiam) (.of_forall (word_cover hS))).trans ?_
  refine liminf_le_of_frequently_le' (.of_forall fun k => ?_)
  calc
    ∑ w : Fin k → Fin n, ediam (word f w '' S) ^ (s : ℝ)
      ≤ ∑ _w : Fin k → Fin n, (c ^ k * ediam S) ^ (s : ℝ) :=
        Finset.sum_le_sum fun w _ => ENNReal.rpow_le_rpow (hdiam k w) s.2
    _ = ediam S ^ (s : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      rw [ENNReal.mul_rpow_of_nonneg (c ^ k) (ediam S) (z := (s : ℝ)) s.2]
      rw [← ENNReal.rpow_natCast_mul, mul_comm (k : ℝ), ENNReal.rpow_mul_natCast,
        show c ^ (s : ℝ) = _ from hs, ← mul_assoc, ← mul_pow]
      rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top _),
        one_pow, one_mul]

/-- At scale `lam ^ k`, only boundedly many level-`k` pieces meet a ball of that radius.
Normalize the centers of the disjoint open balls in those pieces to a fixed compact ball. -/
private lemma bounded_overlap (hl : 0 < lam)
    (hf : ∀ i x y, dist (f i x) (f i y) = lam * dist x y)
    (hsurj : ∀ i, Function.Surjective (f i)) (ho : OpenSetCondition f) (hS : IsAttractor f S) :
    ∃ C : ℕ, ∀ k (x : Space d) (W : Finset (Fin k → Fin n)),
      (∀ w ∈ W, ∃ y ∈ S, dist (word f w y) x ≤ lam ^ k) → W.card ≤ C := by
  classical
  obtain ⟨G, hG, ⟨z, hz⟩, hin, hdis⟩ := ho
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hG z hz
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball z).mp hS.1.isBounded
  obtain ⟨T, _, hT, hcover⟩ := (isCompact_closedBall (0 : Space d) (R + 1)).finite_cover_balls hr
  let := hT.fintype
  refine ⟨Fintype.card T, fun k x W hW => ?_⟩
  have ha : 0 < lam ^ k := pow_pos hl k
  let center (w : Fin k → Fin n) := (lam ^ k)⁻¹ • (word f w z - x)
  have hcenter (w : W) : center w ∈ closedBall 0 (R + 1) := by
    obtain ⟨y, hy, hyx⟩ := hW w w.2
    have hzy : dist z y ≤ R := (dist_comm y z ▸ hR hy : dist z y < R).le
    have hd : dist (word f w.val z) x ≤ lam ^ k * (R + 1) := calc
      _ ≤ dist (word f w.val z) (word f w.val y) + dist (word f w.val y) x :=
        dist_triangle (word f w.val z) (word f w.val y) x
      _ ≤ lam ^ k * R + lam ^ k := by
        rw [word_dist hf]
        exact add_le_add (mul_le_mul_of_nonneg_left hzy ha.le) hyx
      _ = _ := by ring
    change dist ((lam ^ k)⁻¹ • (word f w.val z - x)) 0 ≤ R + 1
    rwa [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha,
      ← dist_eq_norm, inv_mul_le_iff₀ ha]
  have hnet (w : W) : ∃ p : T, center w ∈ ball p.val r := by
    simpa using hcover (hcenter w)
  choose point hpoint using hnet
  have hmem (w : W) : lam ^ k • (point w).val + x ∈ word f w.val '' G := by
    obtain ⟨y, hy⟩ := word_surj hsurj w.val (lam ^ k • (point w).val + x)
    refine ⟨y, hball ?_, hy⟩
    have h := hpoint w
    rw [mem_ball, dist_comm] at h
    have hd := word_dist hf w.val y z
    rw [hy] at hd
    have he : word f w.val z = lam ^ k • center w + x := by
      simp [center, smul_smul, ha.ne']
    rw [he, dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos ha] at hd
    exact (lt_of_eq_of_lt (mul_left_cancel₀ ha.ne' hd.symm) h)
  have inj : Function.Injective point := by
    intro u v huv
    by_contra hne
    have hd := word_disjoint hl hf hin hdis k (show u.val ≠ v.val from mt Subtype.ext hne)
    exact disjoint_left.mp hd (hmem u) (huv.symm ▸ hmem v)
  simpa using Fintype.card_le_of_injective point inj

private noncomputable abbrev bernoulli (n : ℕ) [NeZero n] : Measure (ℕ → Fin n) :=
  infinitePi fun _ : ℕ => ProbabilityTheory.uniformOn (univ : Set (Fin n))

private def prefixSet {k : ℕ} (w : Fin k → Fin n) : Set (ℕ → Fin n) :=
  {a | ∀ j : Fin k, a j = w j}

private lemma prefix_mass [NeZero n] {k : ℕ} (w : Fin k → Fin n) :
    bernoulli n (prefixSet w) = ((n : ℝ≥0∞)⁻¹) ^ k := by
  classical
  let digit (j : ℕ) : Fin n := if h : j < k then w ⟨j, h⟩ else 0
  have he : prefixSet w = Set.pi (Finset.range k) (fun j => {digit j}) := by
    ext a
    change (∀ j : Fin k, a j = w j) ↔ ∀ j ∈ Finset.range k, a j ∈ ({digit j} : Set _)
    constructor
    · intro h j hj
      simpa [digit, Finset.mem_range.mp hj] using h ⟨j, Finset.mem_range.mp hj⟩
    · intro h j
      simpa [digit, j.isLt] using h j (Finset.mem_range.mpr j.isLt)
  rw [he, bernoulli, infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [ProbabilityTheory.uniformOn_univ]

private lemma level_mass [NeZero n] (hl : 0 < lam) (code : (ℕ → Fin n) → Space d)
    (hcode : ∀ a k, code a ∈ word f (fun i : Fin k => a i) '' S) (C : ℕ)
    (hC : ∀ k (x : Space d) (W : Finset (Fin k → Fin n)),
      (∀ w ∈ W, ∃ y ∈ S, dist (word f w y) x ≤ lam ^ k) → W.card ≤ C)
    (t : Set (Space d)) (k : ℕ) (ht : ediam t ≤ ENNReal.ofReal lam ^ k) :
    bernoulli n (code ⁻¹' t) ≤ C * ((n : ℝ≥0∞)⁻¹) ^ k := by
  classical
  obtain h | ⟨x, hx⟩ := t.eq_empty_or_nonempty
  · simp [h]
  let W := Finset.univ.filter fun w : Fin k → Fin n => (word f w '' S ∩ t).Nonempty
  have hcard : W.card ≤ C := by
    apply hC k x
    intro w hw
    obtain ⟨_, ⟨y, hy, rfl⟩, hyt⟩ := (Finset.mem_filter.mp hw).2
    refine ⟨y, hy, ?_⟩
    have hd := (edist_le_ediam_of_mem hyt hx).trans ht
    rwa [edist_dist, ← ENNReal.ofReal_pow hl.le, ENNReal.ofReal_le_ofReal_iff (pow_nonneg hl.le _)]
      at hd
  have hsub : code ⁻¹' t ⊆ ⋃ w ∈ W, prefixSet w := by
    intro a ha
    let w : Fin k → Fin n := fun j => a j
    have hw : w ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, code a, hcode a k, ha⟩
    exact mem_iUnion₂.mpr ⟨w, hw, fun _ => rfl⟩
  calc
    _ ≤ ∑ w ∈ W, bernoulli n (prefixSet w) :=
      (measure_mono hsub).trans (measure_biUnion_finset_le W prefixSet)
    _ = W.card * ((n : ℝ≥0∞)⁻¹) ^ k := by simp [prefix_mass, nsmul_eq_mul]
    _ ≤ _ := by gcongr

private lemma lower_bound [NeZero n] (hl : 0 < lam) (h1 : lam < 1)
    (hf : ∀ i x y, dist (f i x) (f i y) = lam * dist x y)
    (hsurj : ∀ i, Function.Surjective (f i)) (ho : OpenSetCondition f) (hS : IsAttractor f S)
    (s : ℝ≥0) (hs : ENNReal.ofReal lam ^ (s : ℝ) = (n : ℝ≥0∞)⁻¹) :
    (s : ℝ≥0∞) ≤ dimH S := by
  classical
  obtain hs0 | hspos := s.2.eq_or_lt
  · simp [show s = 0 from NNReal.eq hs0.symm]
  obtain ⟨code, hcode⟩ := exists_code hl hf hS
  obtain ⟨C, hC⟩ := bounded_overlap hl hf hsurj ho hS
  -- The outer measure of a set is the Bernoulli mass of its preimage under the coding map.
  let μ := OuterMeasure.map code (bernoulli n).toOuterMeasure
  let c := ENNReal.ofReal lam
  let N : ℝ≥0∞ := n
  have hN : N ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hNtop : N ≠ ∞ := ENNReal.natCast_ne_top _
  let D : ℝ≥0∞ := (C + 1 : ℕ) * N
  have hD : D ≠ 0 := mul_ne_zero (by positivity) hN
  have hDt : D ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hNtop
  have hmass (t : Set (Space d)) (k : ℕ) (ht : ediam t ≤ c ^ k) :
      μ t ≤ C * (N⁻¹) ^ k := level_mass hl code hcode C hC t k ht
  have hbound (t : Set (Space d)) (ht : ediam t ≤ 1) : μ t ≤ D * ediam t ^ (s : ℝ) := by
    by_cases hz : ediam t = 0
    · have hNlt : N⁻¹ < 1 := hs ▸ ENNReal.rpow_lt_one (ENNReal.ofReal_lt_one.mpr h1) hspos
      have htend := ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hNlt) (a := (C : ℝ≥0∞))
        (Or.inr (ENNReal.natCast_ne_top C))
      have hzero : μ t = 0 := by
        simpa using ge_of_tendsto' htend (fun k => hmass t k (hz ▸ bot_le))
      simp [hzero]
    -- Bracket the diameter between successive powers of the contraction ratio.
    have htfin : ediam t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ht
    obtain ⟨k, hlow, hhigh⟩ := exists_nat_pow_near_of_lt_one
      (ENNReal.toReal_pos hz htfin) (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top ht)
      hl h1
    have he (j : ℕ) : ENNReal.ofReal (lam ^ j) = c ^ j := ENNReal.ofReal_pow hl.le j
    have hlow' : c ^ (k + 1) ≤ ediam t := by
      simpa only [he, ENNReal.ofReal_toReal htfin] using ENNReal.ofReal_le_ofReal hlow.le
    have hhigh' : ediam t ≤ c ^ k := by
      simpa only [he, ENNReal.ofReal_toReal htfin] using ENNReal.ofReal_le_ofReal hhigh
    calc
      μ t ≤ C * (N⁻¹) ^ k := hmass t k hhigh'
      _ ≤ ((C + 1 : ℕ) : ℝ≥0∞) * (N⁻¹) ^ k := by
        gcongr
        exact_mod_cast Nat.le_succ C
      _ = D * (c ^ (k + 1)) ^ (s : ℝ) := by
        rw [← ENNReal.rpow_natCast_mul, mul_comm (_ : ℝ) (s : ℝ), ENNReal.rpow_mul_natCast, hs,
          pow_succ]
        dsimp only [D, N]
        rw [mul_mul_mul_comm, ENNReal.mul_inv_cancel hN hNtop, mul_one]
      _ ≤ _ := mul_le_mul_right (ENNReal.rpow_le_rpow hlow' s.2) D
  have hle := OuterMeasure.le_mkMetric (fun r => r ^ (s : ℝ)) (D⁻¹ • μ) 1 zero_lt_one
    (fun t ht => calc
      (D⁻¹ • μ) t = D⁻¹ * μ t := rfl
      _ ≤ D⁻¹ * (D * ediam t ^ (s : ℝ)) := mul_le_mul_right (hbound t ht) _
      _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hD hDt, one_mul])
  have hpre : code ⁻¹' S = univ := eq_univ_of_forall fun a => by
    simpa [word] using hcode a 0
  have hone : μ S = 1 := by
    change bernoulli n (code ⁻¹' S) = 1
    rw [hpre, measure_univ]
  apply le_dimH_of_hausdorffMeasure_ne_zero
  intro hz
  have h := hle S
  rw [OuterMeasure.coe_mkMetric] at h
  change D⁻¹ * μ S ≤ μH[(s : ℝ)] S at h
  simp [hz, hone, hDt] at h

set_option linter.dupNamespace false in
/-- **Moran's equality for affine-symmetric iterated function systems.** Let $n \ge 1$ and let
$(f_i)_{i < n}$ be an affine-symmetric iterated function system on $\mathbb{R}^d$ with common
contraction factor $\lambda \in (0,1)$ that satisfies the open set condition. Then every attractor
$S \subseteq \mathbb{R}^d$ of the system has Hausdorff dimension
$$\dim_H S = -\frac{\log n}{\log \lambda}.$$

Source: P. A. P. Moran, *Additive functions of intervals and Hausdorff measure*, Proc. Cambridge
Philos. Soc. 42 (1946); J. E. Hutchinson, *Fractals and self similarity*, Indiana Univ. Math. J. 30
(1981). Knill, *Some fundamental theorems in mathematics*, §105. Via leanprover/lean-eval@38361be,
problem `moran_equality_affine`. -/
public theorem moran_equality_affine
    {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (h_aff : IsAffineSymmetricIFS f lam)
    (h_osc : OpenSetCondition f)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : IsAttractor f S) :
    dimH S = ENNReal.ofReal (- Real.log n / Real.log lam) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn'
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hl, h1, A, β, he⟩ := h_aff
  have hf (i) (x y : Space d) : dist (f i x) (f i y) = lam * dist x y := by
    simp only [he, dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos hl, (A i).dist_map]
  have hsurj (i) : Function.Surjective (f i) := by
    intro y
    obtain ⟨x, hx⟩ := ((A i).toLinearIsometryEquiv rfl).surjective (lam⁻¹ • (y - β i))
    change A i x = _ at hx
    exact ⟨x, by simp [he, hx, smul_smul, hl.ne']⟩
  have hlog := Real.log_neg hl h1
  let s : ℝ≥0 := ⟨- Real.log n / Real.log lam,
    div_nonneg_of_nonpos (neg_nonpos.mpr (Real.log_nonneg hn')) hlog.le⟩
  have hs : ENNReal.ofReal lam ^ (s : ℝ) = (n : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (p := (s : ℝ)) hl.le s.2, Real.rpow_def_of_pos hl,
      show Real.log lam * (s : ℝ) = - Real.log n by
        change Real.log lam * (- Real.log n / Real.log lam) = _
        field_simp [hlog.ne],
      Real.exp_neg, Real.exp_log hnpos, ENNReal.ofReal_inv_of_pos hnpos, ENNReal.ofReal_natCast]
  exact (le_antisymm (upper_bound (NeZero.ne n) hl h1 hf hS s hs)
    (lower_bound hl h1 hf hsurj h_osc hS s hs)).trans ENNReal.ofReal_coe_nnreal.symm

end MathlibExt.Dynamics.MoranDimensionWanted.Dynamics
