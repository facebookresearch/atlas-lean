/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph

/-!
# The Lovász theta function and the sandwich theorem

An *orthogonal labeling* (orthonormal representation) of a graph `G` assigns a vector to each
vertex so that distinct non-adjacent vertices get orthogonal vectors. Relative to a nonzero
"handle" vector `c`, the *cost* of a vector `x` is `⟪c, x⟫² / (‖c‖² ‖x‖²)`, the squared cosine
of the angle between `c` and `x` (and `0` when `x = 0`). The Lovász number is

  `ϑ(G) = min over orthogonal labelings a and handles c of max_v 1 / cost c (a v)`,

which we define as an infimum of feasible values `t`. We prove the sandwich theorem
`α(G) ≤ ϑ(G) ≤ χ(Ḡ)` with linear algebra only: Bessel's inequality bounds the total cost of a
stable set by `1`, and a colouring of the complement with `k` colours (a cover of the vertices by
`k` cliques of `G`) yields a labeling all of whose costs are `1 / k`.

Sources: L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979),
1-7; D. E. Knuth, "The Sandwich Theorem", Electron. J. Combin. 1 (1994), #A1
(arXiv:math/9312214v1), §1 (orthogonal labelings, cost, Lemma 1), §4 (eq. (4.9)) and §5
(eq. (5.2), the function `ϑ₁` with unit weights).

Conventions. Knuth measures the cost against the first coordinate vector; we allow any nonzero
handle `c`, as Lovász does with a unit vector. An orthogonal change of coordinates (Knuth,
Lemma 0) moves any unit handle to the first coordinate vector, so the two minima agree; that
equivalence is not formalised here. Knuth's `ϑ(G)` is defined through the convex body `TH(G)`
(`LovaszThetaBody`); its equality with the min-max form is Knuth's eq. (5.1), recorded as wanted in
`WantedExt.Combinatorics.LovaszThetaBodyWanted`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

open scoped RealInnerProductSpace
open Finset

variable {V : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Orthogonal labeling of a graph.** A map `a : V → E` into a real inner product space is an
orthogonal labeling (orthonormal representation, up to scaling) of `G` if `⟪a u, a v⟫ = 0`
whenever `u ≠ v` are not adjacent in `G` (Knuth, *The Sandwich Theorem*, 1994, §1). -/
def IsOrthogonalLabeling (G : SimpleGraph V) (a : V → E) : Prop :=
  ∀ ⦃u v : V⦄, u ≠ v → ¬ G.Adj u v → ⟪a u, a v⟫ = 0

/-- **Cost of a vector in an orthogonal labeling.** Relative to a handle `c`, the cost of `x` is
`⟪c, x⟫² / (‖c‖² ‖x‖²)`, the squared cosine of the angle between `c` and `x`, and `0` when
`x = 0` or `c = 0` (Knuth, *The Sandwich Theorem*, 1994, §1, with the first coordinate vector
replaced by a general handle `c`). -/
noncomputable def cost (c x : E) : ℝ :=
  ⟪c, x⟫ ^ 2 / (‖c‖ ^ 2 * ‖x‖ ^ 2)

/-- **Costs are nonnegative.** For all vectors `c` and `x`, `0 ≤ cost c x`. -/
theorem cost_nonneg (c x : E) : 0 ≤ cost c x := by
  unfold cost
  positivity

/-- **Stable sets have total cost at most one.** If `a` is an orthogonal labeling of `G`, `c` is
any vector and `s` is a stable (independent) set of `G`, then `∑_{v ∈ s} cost c (a v) ≤ 1`
(Knuth, *The Sandwich Theorem*, 1994, Lemma 1, eq. (1.1)). The proof is Bessel's inequality for
the normalised vectors `a v / ‖a v‖`, `v ∈ s`, which are orthonormal because `s` is stable. -/
theorem sum_cost_le_one {G : SimpleGraph V} {a : V → E} (ha : IsOrthogonalLabeling G a)
    (c : E) {s : Finset V} (hs : G.IsIndepSet (s : Set V)) :
    ∑ v ∈ s, cost c (a v) ≤ 1 := by
  classical
  by_cases hc : c = 0
  · simp [cost, hc]
  have hcpos : 0 < ‖c‖ ^ 2 := by positivity
  set t := s.filter (fun v => a v ≠ 0) with ht
  have hsplit : ∑ v ∈ s, cost c (a v) = ∑ v ∈ t, cost c (a v) := by
    rw [ht, Finset.sum_filter_of_ne]
    intro v _ h hv
    exact h (by simp [cost, hv])
  let u : t → E := fun v => (‖a v‖⁻¹) • a v
  have hu : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    rintro ⟨v, hv⟩ ⟨w, hw⟩
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    by_cases h : v = w
    · subst h
      have hn : ‖a v‖ ≠ 0 := norm_ne_zero_iff.mpr hv'.2
      simp only [u, ite_true, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
        RCLike.conj_to_real]
      field_simp
    · have hne : (⟨v, hv⟩ : t) ≠ ⟨w, hw⟩ := fun e => h (congrArg Subtype.val e)
      have hadj : ¬ G.Adj v w := hs hv'.1 hw'.1 h
      simp [u, hne, inner_smul_left, inner_smul_right, ha h hadj]
  have hB := hu.sum_inner_products_le (x := c) (s := Finset.univ)
  have key : ∀ i : t, cost c (a i) = ‖⟪u i, c⟫‖ ^ 2 / ‖c‖ ^ 2 := by
    rintro ⟨v, hv⟩
    have hv' := Finset.mem_filter.mp hv
    have hn : ‖a v‖ ≠ 0 := norm_ne_zero_iff.mpr hv'.2
    simp only [u, cost, inner_smul_left, RCLike.conj_to_real, Real.norm_eq_abs, sq_abs,
      real_inner_comm (a v) c]
    field_simp
  rw [hsplit, ← Finset.sum_coe_sort t]
  simp_rw [key, ← Finset.sum_div]
  rw [div_le_one hcpos]
  exact hB

/-- **Feasible values of the theta program.** The set of reals `t ≥ 0` for which some orthogonal
labeling `a : V → ℝ^d` of `G` and some nonzero handle `c ∈ ℝ^d` satisfy `1 ≤ t · cost c (a v)`
for every vertex `v`, i.e. `max_v 1 / cost c (a v) ≤ t` (Knuth, *The Sandwich Theorem*, 1994,
eq. (5.2) with unit weights; Lovász 1979). -/
def thetaFeasible (G : SimpleGraph V) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ ∃ (d : ℕ) (a : V → EuclideanSpace ℝ (Fin d)) (c : EuclideanSpace ℝ (Fin d)),
    c ≠ 0 ∧ IsOrthogonalLabeling G a ∧ ∀ v, 1 ≤ t * cost c (a v)}

/-- **Lovász theta function.** `ϑ(G)` is the infimum of the feasible values of the theta program:
the minimum, over orthogonal labelings `a` of `G` in some `ℝ^d` and nonzero handles `c`, of
`max_v 1 / cost c (a v)` (L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform.
Theory 25 (1979); Knuth, *The Sandwich Theorem*, 1994, eq. (5.2) with unit weights). The empty
graph on no vertices gets `ϑ = 0`. -/
noncomputable def lovaszTheta (G : SimpleGraph V) : ℝ :=
  sInf (thetaFeasible G)

/-- **A colouring of the complement gives a feasible theta value.** If the complement `Gᶜ` is
`k`-colourable, i.e. the vertices of `G` are covered by `k` cliques of `G`, then `k` is a
feasible value of the theta program: label each vertex by the unit vector of its colour class
and take the all-ones handle, so that every cost is `1 / k`. -/
theorem natCast_mem_thetaFeasible_of_colorable {G : SimpleGraph V} {k : ℕ}
    (h : Gᶜ.Colorable k) : (k : ℝ) ∈ thetaFeasible G := by
  classical
  refine ⟨Nat.cast_nonneg k, ?_⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : IsEmpty V := h.isEmpty
    refine ⟨1, fun _ => 0, EuclideanSpace.single 0 1, ?_, fun u => isEmptyElim u,
      fun v => isEmptyElim v⟩
    intro h0
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) h0
    simp at this
  obtain ⟨C⟩ := h
  let c : EuclideanSpace ℝ (Fin k) := ∑ j, EuclideanSpace.single j 1
  have hc_apply : ∀ i, c i = 1 := by
    intro i
    simp [c]
  have hinner : ∀ i, ⟪c, EuclideanSpace.single i (1 : ℝ)⟫ = 1 := by
    intro i
    rw [EuclideanSpace.inner_single_right, hc_apply]
    simp
  have hnorm : ‖c‖ ^ 2 = k := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [show c = ∑ j, EuclideanSpace.single j (1 : ℝ) from rfl]
    rw [inner_sum]
    simp only [show c = ∑ j, EuclideanSpace.single j (1 : ℝ) from rfl] at hinner
    simp [hinner]
  refine ⟨k, fun v => EuclideanSpace.single (C v) 1, c, ?_, ?_, ?_⟩
  · intro h0
    have := hinner ⟨0, hk⟩
    rw [h0, inner_zero_left] at this
    exact zero_ne_one this
  · intro u v huv hadj
    have hcol : C u ≠ C v := C.valid ((SimpleGraph.compl_adj G u v).mpr ⟨huv, hadj⟩)
    rw [EuclideanSpace.inner_single_left]
    simp [Ne.symm hcol]
  · intro v
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [cost, hinner, hnorm, PiLp.norm_single, norm_one]
    field_simp
    exact le_refl _

/-- **Labelings in any finite-dimensional space give feasible values.** If `a` is an orthogonal
labeling of `G` in a finite-dimensional real inner product space `E`, `c ∈ E` is nonzero, `t ≥ 0`
and `1 ≤ t · cost c (a v)` for every vertex `v`, then `t` is a feasible value of the theta program:
an orthonormal basis identifies `E` with `ℝ^d` isometrically. -/
theorem mem_thetaFeasible_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {G : SimpleGraph V} {t : ℝ} (ht : 0 ≤ t)
    (a : V → E) (c : E) (hc : c ≠ 0) (ha : IsOrthogonalLabeling G a)
    (h : ∀ v, 1 ≤ t * cost c (a v)) : t ∈ thetaFeasible G := by
  let e := (stdOrthonormalBasis ℝ E).repr
  refine ⟨ht, _, fun v => e (a v), e c, by simpa using hc, ?_, ?_⟩
  · intro u v huv hadj
    rw [LinearIsometryEquiv.inner_map_map]
    exact ha huv hadj
  · intro v
    simpa [cost, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map] using h v

/-- **Every feasible value dominates the independence number.** For a finite graph `G`, if `t` is a
feasible value of the theta program then `α(G) ≤ t`: for a maximum stable set `S`,
`|S| ≤ t ∑_{v ∈ S} cost c (a v) ≤ t` by Knuth's Lemma 1 (Knuth, *The Sandwich Theorem*, 1994,
eq. (4.9) and Lemma 1). -/
theorem indepNum_le_of_mem_thetaFeasible [Finite V] {G : SimpleGraph V} {t : ℝ}
    (ht : t ∈ thetaFeasible G) : (G.indepNum : ℝ) ≤ t := by
  obtain ⟨ht0, d, a, c, -, ha, hcost⟩ := ht
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have h1 := sum_cost_le_one ha c hs.isIndepSet
  calc (G.indepNum : ℝ) = ∑ _v ∈ s, (1 : ℝ) := by simp [hs.card_eq]
    _ ≤ ∑ v ∈ s, t * cost c (a v) := Finset.sum_le_sum fun v _ => hcost v
    _ = t * ∑ v ∈ s, cost c (a v) := (Finset.mul_sum _ _ _).symm
    _ ≤ t * 1 := mul_le_mul_of_nonneg_left h1 ht0
    _ = t := mul_one t

/-- **Theta is bounded by the clique cover number.** If the complement `Gᶜ` is `k`-colourable,
then `ϑ(G) ≤ k`. -/
theorem lovaszTheta_le_of_colorable {G : SimpleGraph V} {k : ℕ} (h : Gᶜ.Colorable k) :
    lovaszTheta G ≤ k :=
  csInf_le ⟨0, fun _ ht => ht.1⟩ (natCast_mem_thetaFeasible_of_colorable h)

/-- **Theta is nonnegative.** For a finite graph `G`, `0 ≤ ϑ(G)`. -/
theorem lovaszTheta_nonneg [Finite V] (G : SimpleGraph V) : 0 ≤ lovaszTheta G :=
  le_csInf ⟨_, natCast_mem_thetaFeasible_of_colorable (Gᶜ.colorable_chromaticNumber_of_fintype)⟩
    fun _ ht => ht.1

/-- **Independence number is at most theta.** For a finite graph `G`, `α(G) ≤ ϑ(G)`
(Lovász 1979; Knuth, *The Sandwich Theorem*, 1994, eq. (4.9) and Lemma 1). Every feasible value
`t` dominates the independence number. -/
theorem indepNum_le_lovaszTheta [Finite V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ lovaszTheta G :=
  le_csInf ⟨_, natCast_mem_thetaFeasible_of_colorable (Gᶜ.colorable_chromaticNumber_of_fintype)⟩
    fun _ ht => indepNum_le_of_mem_thetaFeasible ht

/-- **Theta is at most the chromatic number of the complement.** For a finite graph `G`,
`ϑ(G) ≤ χ(Ḡ)` (Lovász 1979; Knuth, *The Sandwich Theorem*, 1994, eq. (4.9)). The chromatic
number of a finite graph is finite, so it is read as a natural number. -/
theorem lovaszTheta_le_chromaticNumber_compl [Finite V] (G : SimpleGraph V) :
    lovaszTheta G ≤ (Gᶜ.chromaticNumber.toNat : ℝ) :=
  lovaszTheta_le_of_colorable (Gᶜ.colorable_chromaticNumber_of_fintype)

/-- **Lovász's sandwich theorem.** For a finite graph `G`, `α(G) ≤ ϑ(G) ≤ χ(Ḡ)`: the Lovász
number lies between the independence number of `G` and the chromatic number of its complement
(Lovász 1979; Grötschel, Lovász and Schrijver; Knuth, *The Sandwich Theorem*, 1994, eq. (4.9)). -/
theorem sandwich [Finite V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ lovaszTheta G ∧ lovaszTheta G ≤ (Gᶜ.chromaticNumber.toNat : ℝ) :=
  ⟨indepNum_le_lovaszTheta G, lovaszTheta_le_chromaticNumber_compl G⟩

/-- **Theta equals the independence number on perfect graphs.** If the finite graph `G` is
perfect, then `ϑ(G) = α(G)`. By Lovász's perfect graph theorem the complement `Gᶜ` is perfect,
so `χ(Ḡ) = ω(Ḡ) = α(G)` and the sandwich `α(G) ≤ ϑ(G) ≤ χ(Ḡ)` collapses (Knuth, *The Sandwich
Theorem*, 1994, eq. (4.9) and §31; Schrijver, *A Course in Combinatorial Optimization*,
Corollary 7.7a). This is why `α` and `χ` of perfect graphs are computable in polynomial time
once `ϑ` is. -/
theorem lovaszTheta_eq_indepNum_of_isPerfect [Fintype V] {G : SimpleGraph V}
    (hG : PerfectGraphWanted.IsPerfect G) : lovaszTheta G = G.indepNum := by
  refine le_antisymm ?_ (indepNum_le_lovaszTheta G)
  have hc : PerfectGraphWanted.IsPerfect Gᶜ :=
    (PerfectGraphWanted.lovasz_weak_perfect_graph_general G).mp hG
  have hcol : (Gᶜ.induce Set.univ).Colorable (Gᶜ.induce Set.univ).cliqueNum := by
    rw [← SimpleGraph.chromaticNumber_le_iff_colorable, hc Set.univ]
  have hcol' : Gᶜ.Colorable (Gᶜ.induce Set.univ).cliqueNum :=
    hcol.of_hom (Gᶜ.induceUnivIso.symm.toEmbedding.toHom)
  calc lovaszTheta G ≤ ((Gᶜ.induce Set.univ).cliqueNum : ℝ) := lovaszTheta_le_of_colorable hcol'
    _ ≤ (Gᶜ.cliqueNum : ℝ) := by exact_mod_cast Gᶜ.cliqueNum_induce_le Set.univ
    _ = G.indepNum := by rw [SimpleGraph.cliqueNum_compl]

end MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
