/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Group.WordMetric
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Topology.MetricSpace.ProperSpace
public import MathlibExt.Topology.MetricSpace.GeodesicSpace
public import MathlibExt.Topology.MetricSpace.QuasiIsometry

/-!
# The Švarc–Milnor lemma

Let a group `G` act by isometries, properly discontinuously and cocompactly on a proper geodesic
metric space `X`. Then `G` is finitely generated, and for every base point `x₀` the orbit map
`g ↦ g • x₀` is a quasi-isometry from `G` with a word metric to `X`. Gromov calls this the
"obvious proposition-example [which] constitutes the major link between the asymptotic group
theory and the large-scale Riemannian geometry" (*Asymptotic invariants of infinite groups*, 1993,
§0.2.C₁); compare *Infinite groups as geometric objects*, Proc. ICM 1983, §1.B, for the deck
action of `π₁(V)` on the universal cover of a compact manifold `V`. The lemma goes back to
A. S. Švarc (1955) and J. Milnor (1968).

## Proof

Choose `R ≥ 0` such that the `G`-translates of the closed ball `B(x₀, R)` cover `X` (possible by
cocompactness). Let `S = {g | d(x₀, g • x₀) ≤ 2R + 1}`; it is finite by proper discontinuity and
properness of `X`. Walking along a geodesic from `x₀` to `g • x₀` in unit steps and choosing an
orbit point within `R` of each step writes `g` as a product of at most `d(x₀, g • x₀) + 2` elements
of `S` (`exists_chain`). Conversely each generator moves `x₀` by at most `2R + 1`, so
`d(x₀, g • x₀) ≤ (2R + 1) |g|_S` (`dist_smul_le_mul_wordLength`).

## Main results

* `Group.Generators.dist_smul_le_mul_wordLength`: orbit maps of isometric actions are Lipschitz
  for the word length of any generating family.
* `MathlibExt.SvarcMilnor.exists_generators`: the Švarc–Milnor lemma, with explicit constants
  `L = 2R + 1` and `C = R + 2`.
* `MathlibExt.SvarcMilnor.fg`: such a group is finitely generated.
* `MathlibExt.SvarcMilnor.isQuasiIsometry`: the same statement in terms of
  `Metric.IsQuasiIsometry`, for Mathlib's word metric `Group.Generators.normedGroup`, whose
  distance is the left-invariant `dist g h = |g⁻¹ * h|_P` of Gromov (*Hyperbolic groups*, 1987,
  §2.1).
-/

@[expose] public section

open Metric Set

namespace Group.Generators

variable {G X ι : Type*} [Group G] [PseudoMetricSpace X] [MulAction G X] [IsIsometricSMul G X]

/-- **Orbit maps are Lipschitz for the word length.** If `G` acts isometrically on `X` and every
generator `P.val i` moves `x₀` by at most `M`, then `d(x₀, g • x₀) ≤ M |g|_P` for every `g`. -/
theorem dist_smul_le_mul_wordLength (P : Generators G ι) (x₀ : X) {M : ℝ}
    (hM : ∀ i, dist x₀ (P.val i • x₀) ≤ M) (g : G) :
    dist x₀ (g • x₀) ≤ M * P.wordLength g := by
  obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic g
  rw [show P.wordLength (P.wordProd l) = l.length from hl]
  clear hl
  induction l with
  | nil => simp [wordProd_nil]
  | cons a l ih =>
    obtain ⟨i, b⟩ := a
    rw [wordProd_cons, List.length_cons, mul_smul]
    have hstep : dist x₀ (cond b (P.val i) (P.val i)⁻¹ • x₀) ≤ M := by
      cases b
      · simp only [Bool.cond_false]
        rw [← dist_smul (P.val i), smul_inv_smul, dist_comm]
        exact hM i
      · exact hM i
    calc dist x₀ (cond b (P.val i) (P.val i)⁻¹ • P.wordProd l • x₀)
        ≤ dist x₀ (cond b (P.val i) (P.val i)⁻¹ • x₀) +
          dist (cond b (P.val i) (P.val i)⁻¹ • x₀)
            (cond b (P.val i) (P.val i)⁻¹ • P.wordProd l • x₀) := dist_triangle _ _ _
      _ ≤ M + M * l.length := by
          rw [dist_smul]
          exact add_le_add hstep ih
      _ = M * ((l.length + 1 : ℕ) : ℝ) := by push_cast; ring

end Group.Generators

namespace MathlibExt.SvarcMilnor

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X] [IsIsometricSMul G X]

/-- **Distance between orbit points.** For an isometric action,
`d(g • x, h • x) = d(x, g⁻¹ h • x)`. -/
theorem dist_smul_smul_eq (g h : G) (x : X) : dist (g • x) (h • x) = dist x ((g⁻¹ * h) • x) := by
  rw [← dist_smul g⁻¹, inv_smul_smul, mul_smul]

/-- **Cocompactness gives a covering radius.** If every `G`-orbit meets the compact set `K`, there
is `R ≥ 0` such that every point of `X` is within `R` of the orbit of `x₀`. -/
theorem exists_covering_radius {K : Set X} (hK : IsCompact K) (hcov : ∀ x : X, ∃ g : G, g • x ∈ K)
    (x₀ : X) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x : X, ∃ g : G, dist (g • x₀) x ≤ R := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall x₀
  refine ⟨max r 0, le_max_right _ _, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hcov x
  refine ⟨g⁻¹, ?_⟩
  rw [← dist_smul g, smul_inv_smul, dist_comm]
  exact (mem_closedBall.mp (hr hg)).trans (le_max_left _ _)

/-- **Walking along a geodesic.** Let `X` be geodesic, `R ≥ 0` a covering radius for the orbit of
`x₀`, and `S = {s | d(x₀, s • x₀) ≤ 2R + 1}`. Let `Q : G → ℕ → Prop` hold for `(s, 1)` with
`s ∈ S` and be preserved by right multiplication by elements of `S` while increasing `m` by one.
If `d(x₀, y) ≤ n` and `d(h • x₀, y) ≤ R`, then `Q h m` for some `m ≤ n + 1`. -/
theorem exists_chain (hX : IsGeodesicSpace X) (x₀ : X) {R : ℝ}
    (hR : ∀ x : X, ∃ g : G, dist (g • x₀) x ≤ R) (Q : G → ℕ → Prop)
    (h₁ : ∀ s : G, dist x₀ (s • x₀) ≤ 2 * R + 1 → Q s 1)
    (hmul : ∀ a s m, Q a m → dist x₀ (s • x₀) ≤ 2 * R + 1 → Q (a * s) (m + 1)) :
    ∀ n : ℕ, ∀ (h : G) (y : X), dist x₀ y ≤ n → dist (h • x₀) y ≤ R → ∃ m ≤ n + 1, Q h m := by
  intro n
  induction n with
  | zero =>
    intro h y hy hh
    refine ⟨1, le_rfl, h₁ h ?_⟩
    have h0 : dist x₀ y ≤ 0 := by exact_mod_cast hy
    have hR0 : 0 ≤ R := dist_nonneg.trans hh
    calc dist x₀ (h • x₀) ≤ dist x₀ y + dist y (h • x₀) := dist_triangle _ _ _
      _ ≤ 2 * R + 1 := by rw [dist_comm y]; linarith
  | succ n ih =>
    intro h y hy hh
    by_cases hyn : dist x₀ y ≤ n
    · obtain ⟨m, hm, hQ⟩ := ih h y hyn hh
      exact ⟨m, hm.trans (Nat.le_succ _), hQ⟩
    · push Not at hyn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      obtain ⟨z, hz, hzy⟩ := hX.exists_dist_eq_dist_eq x₀ y hn0 hyn.le
      obtain ⟨h', hh'⟩ := hR z
      obtain ⟨m, hm, hQ⟩ := ih h' z hz.le hh'
      have hy' : dist x₀ y ≤ n + 1 := by exact_mod_cast hy
      have hs : dist x₀ ((h'⁻¹ * h) • x₀) ≤ 2 * R + 1 := by
        rw [← dist_smul_smul_eq]
        calc dist (h' • x₀) (h • x₀) ≤ dist (h' • x₀) z + dist z y + dist y (h • x₀) :=
              dist_triangle4 _ _ _ _
          _ ≤ 2 * R + 1 := by rw [dist_comm y]; linarith
      refine ⟨m + 1, by omega, ?_⟩
      simpa using hmul h' (h'⁻¹ * h) m hQ hs

variable [ProperSpace X] [ProperlyDiscontinuousSMul G X]

/-- **The Švarc–Milnor lemma.** Let `G` act on a proper geodesic metric space `X` by isometries,
properly discontinuously (`ProperlyDiscontinuousSMul`) and cocompactly (every orbit meets a fixed
compact set `K`), and let `x₀ : X`. Then there are a finite set `S ⊆ G` generating `G` and
constants `L ≥ 1`, `C ≥ 0` such that, writing `|g|_S` for the word length,
`d(g • x₀, h • x₀) ≤ L |g⁻¹ h|_S + C`, `|g⁻¹ h|_S ≤ L d(g • x₀, h • x₀) + C`, and every point of
`X` is within `C` of the orbit of `x₀`: the orbit map is a quasi-isometry from `G` with its
(left-invariant) word metric to `X` (Gromov, *Asymptotic invariants of infinite groups*, 1993,
§0.2.C₁; Proc. ICM 1983, §1.B). -/
theorem exists_generators (hX : IsGeodesicSpace X) {K : Set X} (hK : IsCompact K)
    (hcov : ∀ x : X, ∃ g : G, g • x ∈ K) (x₀ : X) :
    ∃ (S : Set G) (_ : S.Finite) (P : Group.Generators G S) (L C : ℝ), 1 ≤ L ∧ 0 ≤ C ∧
      (∀ g h : G, dist (g • x₀) (h • x₀) ≤ L * P.wordLength (g⁻¹ * h) + C ∧
        (P.wordLength (g⁻¹ * h) : ℝ) ≤ L * dist (g • x₀) (h • x₀) + C) ∧
      ∀ x : X, ∃ g : G, dist (g • x₀) x ≤ C := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_covering_radius hK hcov x₀
  set S : Set G := {s | dist x₀ (s • x₀) ≤ 2 * R + 1} with hSdef
  -- `S` is finite by proper discontinuity
  have hSfin : S.Finite := by
    refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G)
      (isCompact_singleton (x := x₀)) (isCompact_closedBall x₀ (2 * R + 1))).subset ?_
    intro s hs
    refine ⟨s • x₀, ⟨x₀, rfl, rfl⟩, ?_⟩
    rw [mem_closedBall, dist_comm]
    exact hs
  -- every element is a product of elements of `S`
  have hgen : ∀ g : G, g ∈ Subgroup.closure S := by
    intro g
    obtain ⟨m, -, hm⟩ := exists_chain hX x₀ hR (fun a _ => a ∈ Subgroup.closure S)
      (fun s hs => Subgroup.subset_closure hs)
      (fun a s _ ha hs => Subgroup.mul_mem _ ha (Subgroup.subset_closure hs))
      (⌈dist x₀ (g • x₀)⌉₊) g (g • x₀) (Nat.le_ceil _) (by simp [hR0])
    exact hm
  have hclosure : Subgroup.closure S = ⊤ := eq_top_iff.mpr fun g _ => hgen g
  let P : Group.Generators G S := Group.Generators.ofSet hclosure
  have hPval : ∀ i : S, P.val i = i := fun _ => rfl
  -- word length bound from the chain
  have hlen : ∀ g : G, (P.wordLength g : ℝ) ≤ dist x₀ (g • x₀) + 2 := by
    intro g
    have h₁ : ∀ s : G, dist x₀ (s • x₀) ≤ 2 * R + 1 → P.wordLength s ≤ 1 := by
      intro s hs
      have := P.wordLength_wordProd_le [(⟨s, hs⟩, true)]
      simpa [Group.Generators.wordProd_singleton, hPval] using this
    obtain ⟨m, hm, hQ⟩ := exists_chain hX x₀ hR (fun a m => P.wordLength a ≤ m) h₁
      (fun a s m ha hs => (P.wordLength_mul_le a s).trans (by have := h₁ s hs; omega))
      (⌈dist x₀ (g • x₀)⌉₊) g (g • x₀) (Nat.le_ceil _) (by simp [hR0])
    have hc : (⌈dist x₀ (g • x₀)⌉₊ : ℝ) < dist x₀ (g • x₀) + 1 :=
      Nat.ceil_lt_add_one dist_nonneg
    have : (P.wordLength g : ℝ) ≤ (⌈dist x₀ (g • x₀)⌉₊ : ℝ) + 1 := by
      exact_mod_cast hQ.trans hm
    linarith
  -- Lipschitz bound for the orbit map
  have hlip : ∀ g : G, dist x₀ (g • x₀) ≤ (2 * R + 1) * P.wordLength g :=
    Group.Generators.dist_smul_le_mul_wordLength P x₀ (fun i => (hPval i).symm ▸ i.2)
  refine ⟨S, hSfin, P, 2 * R + 1, R + 2, by linarith, by linarith, fun g h => ⟨?_, ?_⟩,
    fun x => (hR x).imp fun _ hg => by linarith⟩
  · rw [dist_smul_smul_eq]
    have := hlip (g⁻¹ * h)
    linarith
  · rw [dist_smul_smul_eq]
    have h1 := hlen (g⁻¹ * h)
    have h2 : dist x₀ ((g⁻¹ * h) • x₀) ≤ (2 * R + 1) * dist x₀ ((g⁻¹ * h) • x₀) := by
      have := dist_nonneg (x := x₀) (y := (g⁻¹ * h) • x₀)
      nlinarith
    linarith

/-- **Švarc–Milnor: finite generation.** A group acting by isometries, properly discontinuously and
cocompactly on a proper geodesic metric space is finitely generated. (A nonempty space is needed:
the empty space is covered by the empty compact set for every group.) -/
theorem fg [Nonempty X] (hX : IsGeodesicSpace X) {K : Set X} (hK : IsCompact K)
    (hcov : ∀ x : X, ∃ g : G, g • x ∈ K) : Group.FG G := by
  obtain ⟨S, hS, P, -⟩ := exists_generators hX hK hcov (Classical.arbitrary X)
  have := hS.to_subtype
  rw [Group.fg_iff]
  exact ⟨Set.range P.val, P.closure_eq_top, Set.finite_range _⟩

/-- **Švarc–Milnor as a quasi-isometry.** Under the hypotheses of `exists_generators`, there is a
finite generating family `P` such that the orbit map `g ↦ g • x₀` is a quasi-isometry
(`Metric.IsQuasiIsometry`) from `G` with the word metric `P.normedGroup`
(`dist g h = |g⁻¹ h|_P`) to `X`. -/
theorem isQuasiIsometry (hX : IsGeodesicSpace X) {K : Set X} (hK : IsCompact K)
    (hcov : ∀ x : X, ∃ g : G, g • x ∈ K) (x₀ : X) :
    ∃ (S : Set G) (_ : S.Finite) (P : Group.Generators G S) (L C : ℝ),
      @IsQuasiIsometry G X P.normedGroup.toPseudoMetricSpace _ (fun g => g • x₀) L C := by
  obtain ⟨S, hS, P, L, C, hL, hC, hqi, hden⟩ := exists_generators hX hK hcov x₀
  let _ := P.normedGroup
  have hdist : ∀ g h : G, dist g h = (P.wordLength (g⁻¹ * h) : ℝ) := fun g h =>
    dist_eq_norm_inv_mul g h
  refine ⟨S, hS, P, L, C, ⟨hL, hC, fun g h => ⟨?_, ?_⟩⟩, hden⟩
  · have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
    rw [hdist, div_sub' hL0.ne', div_le_iff₀ hL0]
    have := (hqi g h).2
    nlinarith
  · rw [hdist]
    exact (hqi g h).1

end MathlibExt.SvarcMilnor
