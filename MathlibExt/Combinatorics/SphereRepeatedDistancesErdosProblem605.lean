/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Repeated distances on the sphere

We prove Erdős Problem 605 by lifting a grid of planar points and lines to the unit sphere.
Each incidence gives a pair of orthogonal unit vectors at distance `√2`.

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/SphereRepeatedDistancesErdosProblem605Wanted.lean`:

Source: T. F. Bloom, Erdős Problems, Problem #605, https://www.erdosproblems.com/605 (status
PROVED). UnsolvedMath record UM-30006947 (`EP-605`), dataset ulamai/UnsolvedMath v1.8.0.

The sphere is the unit sphere in `ℝ³` (`EuclideanSpace ℝ (Fin 3)`); by scaling this loses nothing.
Pairs are unordered pairs of distinct points; the common distance `δ` may depend on the point set.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SphereRepeatedDistancesErdosProblem605Wanted

open Classical in
/-- **Number of pairs at a given distance.** For a finite set $P$ of points in $\mathbb{R}^3$ and a
real number $\delta$, this is the number of unordered pairs $\{p, q\}$ of distinct points
$p, q \in P$ with Euclidean distance $|p - q| = \delta$, computed as half the number of ordered
pairs $(p, q)$ of distinct points of $P$ at distance $\delta$ and taken as a real number. -/
noncomputable def pairsAtDistance (P : Finset (EuclideanSpace ℝ (Fin 3))) (δ : ℝ) : ℝ :=
  ((P.offDiag.filter fun pq => dist pq.1 pq.2 = δ).card : ℝ) / 2

/-- **Erdős Problem 605 (repeated distances on the sphere).** The proposition that there is a
function $f : \mathbb{N} \to \mathbb{R}$ with $f(n) \to \infty$ as $n \to \infty$ such that for
every $n \in \mathbb{N}$ there are a set $P$ of $n$ distinct points on the unit sphere
$\{x \in \mathbb{R}^3 : \|x\| = 1\}$ and a real number $\delta$ for which the number of unordered
pairs of distinct points of $P$ at distance $\delta$ is at least $f(n) \cdot n$. -/
def sphereRepeatedDistanceSuperlinear : Prop :=
  ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop ∧ ∀ n : ℕ,
    ∃ P : Finset (EuclideanSpace ℝ (Fin 3)), P.card = n ∧ (∀ p ∈ P, ‖p‖ = 1) ∧
      ∃ δ : ℝ, f n * n ≤ pairsAtDistance P δ

open NormedSpace
open scoped RealInnerProductSpace

private abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Normalization is injective on an affine coordinate plane of height one. -/
private lemma eq_of_normalize_eq {v w : Space} (i : Fin 3) (hv : v i = 1) (hw : w i = 1)
    (h : normalize v = normalize w) : v = w := by
  have hi := congrArg (fun p : Space => p i) h
  simp only [NormedSpace.normalize, PiLp.smul_apply, smul_eq_mul, hv, hw, mul_one, inv_inj] at hi
  calc
    v = ‖v‖ • normalize v := (norm_smul_normalize v).symm
    _ = ‖w‖ • normalize w := by rw [hi, h]
    _ = w := norm_smul_normalize w

private lemma norm_normalize_of_coord {v : Space} (i : Fin 3) (h : v i = 1) :
    ‖normalize v‖ = 1 := by
  apply norm_normalize
  rintro rfl
  norm_num at h

private noncomputable def point (p : ℕ × ℕ) : Space :=
  normalize !₂[(p.1 : ℝ), (p.2 : ℝ), 1]

private noncomputable def pole (l : ℕ × ℕ) : Space :=
  normalize !₂[-(l.1 : ℝ), 1, -(l.2 : ℝ)]

private lemma norm_point (p : ℕ × ℕ) : ‖point p‖ = 1 :=
  norm_normalize_of_coord 2 rfl

private lemma norm_pole (l : ℕ × ℕ) : ‖pole l‖ = 1 :=
  norm_normalize_of_coord 1 rfl

private lemma point_injective : Function.Injective point := by
  intro p q h
  have he := eq_of_normalize_eq 2 rfl rfl h
  apply Prod.ext
  · exact Nat.cast_injective (R := ℝ) (congrArg (fun v : Space => v 0) he)
  · exact Nat.cast_injective (R := ℝ) (congrArg (fun v : Space => v 1) he)

private lemma pole_injective : Function.Injective pole := by
  intro l l' h
  have he := eq_of_normalize_eq 1 rfl rfl h
  apply Prod.ext
  · have h₀ : -(l.1 : ℝ) = -(l'.1 : ℝ) := congrArg (fun v : Space => v 0) he
    exact_mod_cast neg_inj.mp h₀
  · have h₂ : -(l.2 : ℝ) = -(l'.2 : ℝ) := congrArg (fun v : Space => v 2) he
    exact_mod_cast neg_inj.mp h₂

/-- The pole of the line `y = m*x + b` is orthogonal to each lifted point on it. -/
private lemma incidence_dist (x m b : ℕ) :
    dist (point (x, m * x + b)) (pole (m, b)) = Real.sqrt 2 := by
  have h : ⟪point (x, m * x + b), pole (m, b)⟫ = 0 := by
    simp [point, pole, NormedSpace.normalize, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (_ - _)), norm_sub_sq_real,
    norm_point, norm_pole, h]
  norm_num

open Finset

private noncomputable def incidencePair (t : ℕ × ℕ × ℕ) : Space × Space :=
  (point (t.1, t.2.1 * t.1 + t.2.2), pole t.2)

private lemma incidencePair_injective : Function.Injective incidencePair := by
  rintro ⟨x, l⟩ ⟨x', l'⟩ h
  have hpoint := point_injective (congrArg Prod.fst h)
  exact Prod.ext (congrArg (fun p : ℕ × ℕ => p.1) hpoint) (pole_injective (congrArg Prod.snd h))

/-- A grid of width `k` and height `2k²` meets `k³` lines in at least `k⁴` incidences.
Enlarge the set of lifted points and poles to the prescribed size on the same sphere. -/
private lemma grid_configuration (k n : ℕ) (hkn : 3 * k ^ 3 ≤ n) :
    ∃ P : Finset Space, P.card = n ∧ (∀ p ∈ P, ‖p‖ = 1) ∧
      (k : ℝ) ^ 4 / 2 ≤ pairsAtDistance P (Real.sqrt 2) := by
  classical
  let grid := ((range k) ×ˢ (range (2 * k ^ 2))).image point
  let lines := ((range k) ×ˢ (range (k ^ 2))).image pole
  let S := grid ∪ lines
  have hcard : S.card ≤ n := calc
    S.card ≤ grid.card + lines.card := card_union_le _ _
    _ ≤ ((range k) ×ˢ (range (2 * k ^ 2))).card + ((range k) ×ˢ (range (k ^ 2))).card :=
      Nat.add_le_add card_image_le card_image_le
    _ = 3 * k ^ 3 := by
      simp
      ring
    _ ≤ n := hkn
  let extra := (range n).image (fun i => point (i, 0))
  have hextra : extra.card = n := by
    rw [card_image_of_injective, card_range]
    exact fun _ _ h => congrArg Prod.fst (point_injective h)
  obtain ⟨P, hSP, hP, hPn⟩ := exists_subsuperset_card_eq
    (subset_union_left (s₂ := extra) : S ⊆ S ∪ extra) hcard
    (hextra ▸ card_le_card (subset_union_right : extra ⊆ S ∪ extra))
  refine ⟨P, hPn, ?_, ?_⟩
  · intro p hp
    have hp' := hP hp
    simp only [S, grid, lines, extra, mem_union, mem_image] at hp'
    rcases hp' with ((⟨a, _, rfl⟩ | ⟨l, _, rfl⟩) | ⟨i, _, rfl⟩)
    · exact norm_point a
    · exact norm_pole l
    · exact norm_point _
  · let triples := (range k) ×ˢ ((range k) ×ˢ (range (k ^ 2)))
    let hits := P.offDiag.filter fun pq => dist pq.1 pq.2 = Real.sqrt 2
    have hcount : triples.card ≤ hits.card := by
      apply card_le_card_of_injOn incidencePair _ incidencePair_injective.injOn
      rintro ⟨x, m, b⟩ ht
      simp only [triples, Finset.mem_coe, mem_product, mem_range] at ht
      obtain ⟨hx, hm, hb⟩ := ht
      have hy : m * x + b < 2 * k ^ 2 := by
        nlinarith [Nat.mul_le_mul hm.le hx.le]
      have hd := incidence_dist x m b
      refine mem_filter.mpr ⟨mem_offDiag.mpr ⟨hSP (mem_union_left _ ?_),
        hSP (mem_union_right _ ?_), ?_⟩, hd⟩
      · exact mem_image.mpr ⟨_, mem_product.mpr ⟨mem_range.mpr hx, mem_range.mpr hy⟩, rfl⟩
      · exact mem_image.mpr ⟨_, mem_product.mpr ⟨mem_range.mpr hm, mem_range.mpr hb⟩, rfl⟩
      · exact dist_pos.mp (hd.trans_gt (Real.sqrt_pos.2 (by norm_num)))
    have hsize : triples.card = k ^ 4 := by
      simp [triples]
      ring
    rw [hsize] at hcount
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast hcount

/--
**Erdős Problem 605 is true.** There is a function $f : \mathbb{N} \to \mathbb{R}$ with
$f(n) \to \infty$ as $n \to \infty$ such that for every $n \in \mathbb{N}$ there are a set $P$ of
$n$ distinct points on the unit sphere $\{x \in \mathbb{R}^3 : \|x\| = 1\}$ and a real number
$\delta$ for which the number of unordered pairs of distinct points of $P$ at distance $\delta$
is at least $f(n) \cdot n$.

Erdős, Hickerson and Pach (Theorem 2(ii)) found an absolute constant $c > 0$ such that for every
$n$ there are $n$ points on the unit sphere each at distance $\sqrt{2}$ from at least
$c n^{1/3}$ others, hence at least $c n^{4/3} / 2$ pairs at distance $\sqrt{2}$;
erdosproblems.com/605 lists the problem as proved.

Source: T. F. Bloom,
Erdős Problems, Problem #605, https://www.erdosproblems.com/605 (status PROVED); resolution: P.
Erdős, D. Hickerson and J. Pach, A problem of Leo Moser about repeated distances on the sphere,
Amer. Math. Monthly (1989), 569-575, Theorem 2(ii): for every n there are n points on the unit
sphere S² each at distance √2 from at least c₂ n^{1/3} others; Theorem 2(i): for every 0 < α < 2, n
points each at distance α from at least c₁ log* n others, https://www.erdosproblems.com/605.
-/
public theorem sphereRepeatedDistanceSuperlinear_holds : sphereRepeatedDistanceSuperlinear := by
  let k (n : ℕ) := Nat.nthRoot 3 (n / 3)
  have hk : Filter.Tendsto k Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro a
    refine ⟨a ^ 3 * 3, fun n hn => ?_⟩
    exact (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).2 ((Nat.le_div_iff_mul_le (by decide)).2 hn)
  refine ⟨fun n => (k n : ℝ) / 48,
    (tendsto_natCast_atTop_atTop.comp hk).atTop_div_const (by norm_num), fun n => ?_⟩
  have hlo : k n ^ 3 ≤ n / 3 := Nat.pow_nthRoot_le (.inl (by decide))
  obtain ⟨P, hcard, hnorm, hpairs⟩ := grid_configuration (k n) n (by omega)
  refine ⟨P, hcard, hnorm, Real.sqrt 2, le_trans ?_ hpairs⟩
  -- For positive k, n < 3 (k+1)³ ≤ 24 k³, so k⁴/2 pairs suffice.
  by_cases hz : k n = 0
  · simp [hz]
  · have hstep : k n + 1 ≤ 2 * k n := by omega
    have hhi := (Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) (n / 3)).trans_le
      (Nat.pow_le_pow_left hstep 3)
    have hn : n ≤ 24 * k n ^ 3 := by
      change n / 3 < (2 * k n) ^ 3 at hhi
      ring_nf at hhi
      omega
    have hmul := Nat.mul_le_mul_left (k n) hn
    have hr : (k n : ℝ) * n ≤ k n * (24 * (k n : ℝ) ^ 3) := by exact_mod_cast hmul
    linarith

end MathlibExt.Combinatorics.SphereRepeatedDistancesErdosProblem605Wanted
