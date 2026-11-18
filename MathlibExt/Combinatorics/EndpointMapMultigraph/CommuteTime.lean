/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.ThomsonPrinciple
public import MathlibExt.Combinatorics.EndpointMapMultigraph.Conductance

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The commute-time identity

The network random walk on a finite loopless multigraph with positive conductances `w` sits at a
vertex `x` and crosses an incident edge `e` with probability `w_e / π(x)`, where
`π(x) = ∑_{e ∋ x} w_e` is the weighted degree. The expected hitting times `h(x) = E_x[τ_z]` of a
vertex `z` solve the first-step equations `h(z) = 0` and
`h(x) = 1 + ∑_{e ∋ x} (w_e / π(x)) h(other end of e)` for `x ≠ z`.

The commute-time identity of Chandra, Raghavan, Ruzzo, Smolensky and Tiwari says that
`E_a[τ_z] + E_z[τ_a] = γ R_eff(a, z)` with `γ = ∑_x π(x) = 2 ∑_e w_e`
(R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016,
corrected online version of 19 August 2026, Corollary 2.21; for unit conductances `γ = 2|E|`).

Here the identity is proved for the solutions of the first-step equations
(`commute_time_identity`), which exist and are unique on a connected loopless multigraph
(`exists_isHittingTimeSolution`, `isHittingTimeSolution_unique`). That the expected hitting times
of the walk solve them is first-step analysis and is not formalised here; this is therefore a
statement about the linear system that characterises hitting times, not about a stochastic
process.

The weighted degree is `EndpointMapMultigraph.weightedDegree` (from the conductance module), which
counts a loop at both of its ends; so does `neighbourSum`. With a loop, the first-step equations
below would describe the walk that takes a loop `e` with probability `2 w_e / π(x)`, not the
source's walk, which counts a loop once. The hitting-time and commute-time theorems therefore
assume that the multigraph has no loops.

* `laplacian_mulVec_apply`: `(L h)(x) = π(x) h(x) - ∑_{e ∋ x} w_e h(other end of e)`;
* `sum_weightedDegree`: `∑_x π(x) = 2 ∑_e w_e`;
* `exists_isHittingTimeSolution`, `isHittingTimeSolution_unique`: the first-step equations have
  exactly one solution on a connected loopless multigraph;
* `hitting_time_identity`: Tetali's formula `h_z(a) = ∑_x π(x) v(x)` for the potential `v` of a
  unit current from `a` to `z` with `v(z) = 0`;
* `commute_time_identity`: `h_z(a) + h_a(z) = 2 (∑_e w_e) R_eff(a, z)` for loopless multigraphs;
* `commute_time_identity_one`: for unit conductances, `h_z(a) + h_a(z) = 2 |E| R_eff(a, z)`.
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]
  (end₁ end₂ : E → V)

/-- **Neighbour sum of the network walk.** `∑_{e ∋ x} w_e h(other end of e)`: in a loopless
multigraph, `π(x)` times the expected value of `h` after one step of the network random walk from
`x` (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016,
corrected online version of 19 August 2026, Section 2.2: the walk moves along an edge chosen with
probability proportional to its conductance). A loop at `x` is counted at both of its ends,
contributing `2 w_e h(x)`. -/
noncomputable def neighbourSum (w : E → ℝ) (h : V → ℝ) (x : V) : ℝ :=
  ∑ e, ((if end₁ e = x then w e * h (end₂ e) else 0) + if end₂ e = x then w e * h (end₁ e) else 0)

/-- **First-step equations for hitting times.** For positive conductances on a connected
multigraph, `h(z) = 0` and, for `x ≠ z`, `h(x) = 1 + ∑_{e ∋ x} (w_e / π(x)) h(other end of e)`.
On a loopless multigraph this is the linear system satisfied by the expected hitting times of
`z` for the network random walk (R. Lyons and Y. Peres, *Probability on Trees and Networks*,
Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.7; the walk
crosses an edge with probability proportional to its conductance, Section 2.2). Positivity and
connectivity make every `x ≠ z` have positive weighted degree, so that the `w_e / π(x)` are
transition probabilities: a vertex of weighted degree `0` would get the equation `h(x) = 1`
(`x / 0 = 0`) although `z` cannot be reached from it. With a loop it is the system of a different
walk: `weightedDegree` and `neighbourSum` count a loop at both ends, so the loop is taken with
probability `2 w_e / π(x)` instead of the source's `w_e / π(x)`. -/
def IsHittingTimeSolution (w : E → ℝ) (_hw : ∀ e, 0 < w e)
    (_hconn : (underlyingGraph end₁ end₂).Connected) (z : V) (h : V → ℝ) : Prop :=
  h z = 0 ∧ ∀ x, x ≠ z → h x = 1 + neighbourSum end₁ end₂ w h x / weightedDegree end₁ end₂ w x

/-- **The Laplacian of a multigraph applied to a potential.**
`(L h)(x) = π(x) h(x) - ∑_{e ∋ x} w_e h(other end of e)`, that is `L = D - A` for the weighted
degree `D` and the weighted adjacency `A` (R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Exercise 2.62, the network Laplacian `Δ_G`). A loop `e` at `x` contributes `2 w_e h(x)` to both
terms, and the two contributions cancel. -/
theorem laplacian_mulVec_apply (w : E → ℝ) (h : V → ℝ) (x : V) :
    (laplacian end₁ end₂ w *ᵥ h) x =
      weightedDegree end₁ end₂ w x * h x - neighbourSum end₁ end₂ w h x := by
  have hL : laplacian end₁ end₂ w *ᵥ h =
      orientedIncidence end₁ end₂ *ᵥ (fun e => w e * (h (end₁ e) - h (end₂ e))) := by
    rw [laplacian, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
    congr 1
    funext e
    rw [mulVec_diagonal, vecMul_orientedIncidence_apply]
  rw [hL, weightedDegree, neighbourSum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  change ∑ e, orientedIncidence end₁ end₂ x e * (w e * (h (end₁ e) - h (end₂ e))) = _
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [orientedIncidence_apply]
  by_cases h₁ : end₁ e = x <;> by_cases h₂ : end₂ e = x
  all_goals simp only [h₁, h₂, ↓reduceIte]; ring

omit [DecidableEq E] in
/-- **Sum of the weighted degrees.** `∑_x π(x) = 2 ∑_e w_e`: every edge is counted at both of its
ends (the constant `γ` of R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge
University Press 2016, corrected online version of 19 August 2026, Corollary 2.21, in a loopless
multigraph). -/
theorem sum_weightedDegree (w : E → ℝ) :
    ∑ x, weightedDegree end₁ end₂ w x = 2 * ∑ e, w e := by
  simp only [weightedDegree]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  ring

/-- The Laplacian kills the left constant vector: `∑_x (L h)(x) = 0`. -/
private theorem sum_laplacian_mulVec (w : E → ℝ) (h : V → ℝ) :
    ∑ x, (laplacian end₁ end₂ w *ᵥ h) x = 0 := by
  have h1 : (1 : V → ℝ) ⬝ᵥ (laplacian end₁ end₂ w *ᵥ h) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, laplacian_transpose,
      laplacian_mulVec_one, zero_dotProduct]
  simpa [dotProduct] using h1

omit [DecidableEq E] [Fintype V] in
/-- In a connected multigraph with positive conductances, a vertex with another vertex in the
graph has positive weighted degree. -/
private theorem weightedDegree_pos {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hconn : (underlyingGraph end₁ end₂).Connected) {x z : V} (hxz : x ≠ z) :
    0 < weightedDegree end₁ end₂ w x := by
  obtain ⟨p⟩ := hconn.preconnected x z
  cases p with
  | nil => exact absurd rfl hxz
  | cons hadj _ =>
    obtain ⟨-, e, he⟩ := (underlyingGraph_adj end₁ end₂).1 hadj
    have hnonneg : ∀ f ∈ (Finset.univ : Finset E), 0 ≤
        w f * ((if end₁ f = x then 1 else 0) + if end₂ f = x then 1 else 0) := by
      intro f _
      have := (hw f).le
      split_ifs <;> nlinarith
    have hpos : 0 < w e * ((if end₁ e = x then 1 else 0) + if end₂ e = x then 1 else 0) := by
      have := (hw e)
      rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
      · simp only [h1, ↓reduceIte]; split_ifs <;> nlinarith
      · simp only [h2, ↓reduceIte]; split_ifs <;> nlinarith
    exact lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg (Finset.mem_univ e))

/-- A solution of the first-step equations for `z` satisfies `L h = π - γ δ_z`. -/
private theorem laplacian_mulVec_of_isHittingTimeSolution {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hconn : (underlyingGraph end₁ end₂).Connected) {z : V} {h : V → ℝ}
    (hh : IsHittingTimeSolution end₁ end₂ w hw hconn z h) :
    laplacian end₁ end₂ w *ᵥ h = fun x => weightedDegree end₁ end₂ w x -
      if x = z then ∑ y, weightedDegree end₁ end₂ w y else 0 := by
  classical
  have hoff : ∀ x, x ≠ z → (laplacian end₁ end₂ w *ᵥ h) x = weightedDegree end₁ end₂ w x := by
    intro x hx
    have hπ := (weightedDegree_pos end₁ end₂ hw hconn hx).ne'
    rw [laplacian_mulVec_apply, hh.2 x hx]
    field_simp
    ring
  funext x
  by_cases hx : x = z
  · subst hx
    have hsum := sum_laplacian_mulVec end₁ end₂ w h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)] at hsum
    rw [Finset.sum_congr rfl fun y hy => hoff y (Finset.ne_of_mem_erase hy)] at hsum
    simp only [↓reduceIte]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    linarith
  · simp only [hoff x hx, hx, ↓reduceIte, sub_zero]

/-- **Hitting-time identity.** In a finite connected loopless multigraph with positive
conductances, if `h`
solves the first-step equations of the expected hitting times of `z` and `v` is the potential of a
unit current from `a` to `z` that vanishes at `z` (`L v = δ_a - δ_z`, `v(z) = 0`), then
`h(a) = ∑_x π(x) v(x)` (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge
University Press 2016, corrected online version of 19 August 2026, Proposition 2.20, due to
Tetali, with `Z = {z}`). -/
theorem hitting_time_identity {w : E → ℝ} (hw : ∀ e, 0 < w e) (_hloop : ∀ e, end₁ e ≠ end₂ e)
    (hconn : (underlyingGraph end₁ end₂).Connected) {a z : V} {h v : V → ℝ}
    (hh : IsHittingTimeSolution end₁ end₂ w hw hconn z h)
    (hv : laplacian end₁ end₂ w *ᵥ v = Pi.single a 1 - Pi.single z 1) (hvz : v z = 0) :
    h a = ∑ x, weightedDegree end₁ end₂ w x * v x := by
  classical
  have hLh := laplacian_mulVec_of_isHittingTimeSolution end₁ end₂ hw hconn hh
  have hsym : v ⬝ᵥ (laplacian end₁ end₂ w *ᵥ h) = h ⬝ᵥ (laplacian end₁ end₂ w *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, laplacian_transpose,
      dotProduct_comm]
  rw [hv, hLh, dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one,
    hh.1, sub_zero] at hsym
  rw [← hsym, dotProduct]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, hvz, zero_mul, sub_zero]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

omit [DecidableEq E] [Fintype V] in
/-- **Existence of hitting times.** On a finite connected loopless multigraph with positive
conductances, the first-step equations of the expected hitting times of any vertex `z` have a
solution. In R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press
2016, corrected online version of 19 August 2026, the solution is the vector of expected hitting
times, finite by the hitting-time identity (Proposition 2.20); here existence is proved by linear
algebra, solving `L h = π - γ δ_z`. -/
theorem exists_isHittingTimeSolution [Finite V] {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) (hconn : (underlyingGraph end₁ end₂).Connected) (z : V) :
    ∃ h, IsHittingTimeSolution end₁ end₂ w hw hconn z h := by
  have := Fintype.ofFinite V
  classical
  set G := underlyingGraph end₁ end₂
  set γ := ∑ y, weightedDegree end₁ end₂ w y
  set b : V → ℝ := fun x => weightedDegree end₁ end₂ w x - if x = z then γ else 0 with hb
  have hmem : b ∈ LinearMap.range (orientedIncidence end₁ end₂).mulVecLin := by
    rw [mem_range_orientedIncidence_iff end₁ end₂ hloop]
    intro c
    have hall : ∀ x : V, G.connectedComponentMk x = c := fun x => by
      have := hconn.preconnected.subsingleton_connectedComponent
      exact Subsingleton.elim _ _
    have hfilter : (Finset.univ.filter fun x => G.connectedComponentMk x = c) = Finset.univ :=
      Finset.filter_true_of_mem fun x _ => hall x
    change ∑ x ∈ Finset.univ.filter (fun x => G.connectedComponentMk x = c), b x = 0
    rw [hfilter, hb]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, γ,
      sub_self]
  rw [← range_laplacian_eq_range_orientedIncidence end₁ end₂ hw hloop] at hmem
  obtain ⟨g, hg⟩ := hmem
  change laplacian end₁ end₂ w *ᵥ g = b at hg
  refine ⟨g - g z • 1, by simp, fun x hx => ?_⟩
  have hπ := (weightedDegree_pos end₁ end₂ hw hconn hx).ne'
  have hLx : (laplacian end₁ end₂ w *ᵥ (g - g z • 1)) x = weightedDegree end₁ end₂ w x := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, laplacian_mulVec_one, smul_zero, sub_zero, hg,
      hb]
    simp [hx]
  rw [laplacian_mulVec_apply] at hLx
  field_simp
  linarith

omit [DecidableEq E] [Fintype V] in
/-- **Uniqueness of hitting times.** On a finite connected loopless multigraph with positive
conductances, the first-step equations of the expected hitting times of `z` have at most one
solution (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press
2016, corrected online version of 19 August 2026, Section 2.1, Uniqueness Principle, applied to
the difference of two solutions, which is harmonic off `z` and vanishes at `z`). -/
theorem isHittingTimeSolution_unique [Finite V] {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (hloop : ∀ e, end₁ e ≠ end₂ e) (hconn : (underlyingGraph end₁ end₂).Connected) {z : V}
    {h h' : V → ℝ} (hh : IsHittingTimeSolution end₁ end₂ w hw hconn z h)
    (hh' : IsHittingTimeSolution end₁ end₂ w hw hconn z h') : h = h' := by
  have := Fintype.ofFinite V
  classical
  have hL : laplacian end₁ end₂ w *ᵥ (h - h') = 0 := by
    rw [Matrix.mulVec_sub, laplacian_mulVec_of_isHittingTimeSolution end₁ end₂ hw hconn hh,
      laplacian_mulVec_of_isHittingTimeSolution end₁ end₂ hw hconn hh', sub_self]
  have hconst := (laplacian_mulVec_eq_zero_iff end₁ end₂ hw hloop _).1 hL
  funext x
  have := hconst x z (hconn.preconnected x z)
  simp only [Pi.sub_apply, hh.1, hh'.1, sub_zero] at this
  linarith

/-- **Commute-time identity.** In a finite connected loopless multigraph with positive
conductances `w`,
if `h_z` and `h_a` solve the first-step equations of the expected hitting times of `z` and of `a`,
then `h_z(a) + h_a(z) = γ R_eff(a, z)` with `γ = 2 ∑_e w_e = ∑_x π(x)` (R. Lyons and Y. Peres,
*Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of
19 August 2026, Corollary 2.21, due to Chandra, Raghavan, Ruzzo, Smolensky and Tiwari). For
`a = z` both sides are `0`. The proof does not use looplessness; it is assumed because with a loop
the first-step equations describe a different walk (see `IsHittingTimeSolution`). -/
theorem commute_time_identity {w : E → ℝ} (hw : ∀ e, 0 < w e) (_hloop : ∀ e, end₁ e ≠ end₂ e)
    (hconn : (underlyingGraph end₁ end₂).Connected) {a z : V} {ha hz : V → ℝ}
    (hha : IsHittingTimeSolution end₁ end₂ w hw hconn a ha)
    (hhz : IsHittingTimeSolution end₁ end₂ w hw hconn z hz) :
    hz a + ha z = 2 * (∑ e, w e) * effectiveResistance end₁ end₂ w a z := by
  classical
  by_cases haz : a = z
  · subst haz
    have hC : effectiveConductance end₁ end₂ w a a = 0 := by
      have hempty : {q | ∃ x : V → ℝ, x a = 0 ∧ x a = 1 ∧
          q = x ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x)} = ∅ := by
        ext q
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro x h0 h1
        rw [h0] at h1
        exact absurd h1 zero_ne_one
      rw [effectiveConductance, hempty, Real.sInf_empty]
    rw [effectiveResistance, hC, _root_.inv_zero, mul_zero, hhz.1, hha.1, add_zero]
  set γ := ∑ y, weightedDegree end₁ end₂ w y with hγ
  have hγpos : 0 < γ := by
    have hnonneg : ∀ y ∈ (Finset.univ : Finset V), 0 ≤ weightedDegree end₁ end₂ w y :=
      fun y _ => weightedDegree_nonneg end₁ end₂ (fun e => (hw e).le) y
    exact lt_of_lt_of_le (weightedDegree_pos end₁ end₂ hw hconn haz)
      (Finset.single_le_sum hnonneg (Finset.mem_univ a))
  have hγne : γ ≠ 0 := hγpos.ne'
  have hLz := laplacian_mulVec_of_isHittingTimeSolution end₁ end₂ hw hconn hhz
  have hLa := laplacian_mulVec_of_isHittingTimeSolution end₁ end₂ hw hconn hha
  set v : V → ℝ := γ⁻¹ • (hz - ha) with hv
  have hLv : laplacian end₁ end₂ w *ᵥ v = Pi.single a 1 - Pi.single z 1 := by
    rw [hv, Matrix.mulVec_smul, Matrix.mulVec_sub, hLz, hLa]
    funext x
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]
    by_cases hxa : x = a <;> by_cases hxz : x = z
    · exact absurd (hxa.symm.trans hxz) haz
    all_goals simp only [hxa, hxz, haz, Ne.symm haz, ↓reduceIte, ← hγ]
    all_goals simp [inv_mul_cancel₀ hγne]
  have hR := (effectiveResistance_eq_sub_of_laplacian_mulVec end₁ end₂ (fun e => (hw e).le) haz
    hLv).1
  rw [← sum_weightedDegree end₁ end₂ w, ← hγ, hR, hv]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hhz.1, hha.1]
  field_simp
  ring

/-- **Commute-time identity for unit conductances.** In a finite connected loopless multigraph
with every conductance `1`, solutions `h_z`,
`h_a` of the first-step equations for simple random walk satisfy
`h_z(a) + h_a(z) = 2 |E| R_eff(a, z)` (R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Corollary 2.21 with `c ≡ 1`). -/
theorem commute_time_identity_one (hloop : ∀ e, end₁ e ≠ end₂ e)
    (hconn : (underlyingGraph end₁ end₂).Connected) {a z : V} {ha hz : V → ℝ}
    (hha : IsHittingTimeSolution end₁ end₂ (fun _ => 1) (fun _ => one_pos) hconn a ha)
    (hhz : IsHittingTimeSolution end₁ end₂ (fun _ => 1) (fun _ => one_pos) hconn z hz) :
    hz a + ha z = 2 * Fintype.card E * effectiveResistance end₁ end₂ (fun _ => 1) a z := by
  rw [commute_time_identity end₁ end₂ (fun _ => one_pos) hloop hconn hha hhz]
  simp

end EndpointMapMultigraph
