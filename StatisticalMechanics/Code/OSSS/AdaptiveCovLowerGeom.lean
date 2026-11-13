/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCovLowerClose
import Code.OSSS.RevealmentTranslation

open scoped BigOperators
open Finset Set

namespace StatMech
namespace OSSS
namespace AdaptiveCovLowerGeom

open Lattice Monotonic RevealmentConstruction AdaptiveCovLowerClose
open RevealmentTranslation
open MonotonicFK
open LindebergTree FamilyEqzzzResolution FrontierFamilyClose DecisionTree
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {d : ℕ}


noncomputable def crossIndG (edge : E → Sym2 (Site d)) (o : Site d) (n : ℕ) :
    ConfigSpace E → ℝ :=
  (crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))


noncomputable def boxRevealG (μ : ConfigSpace E → ℝ)
    (edge : E → Sym2 (Site d)) (endU endV : E → Site d)
    (k : ℕ) (e : E) : ℝ :=
  Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
                then (1 : ℝ) else 0)
    + Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                then (1 : ℝ) else 0)



theorem hcov_crossTree_mass
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List E) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n) (D : ℝ) (hD : 0 < D)
    (hsum : ∀ e : E,
      (∑ k : ↥(Finset.Icc 1 n), boxRevealG μ edge endU endV (k : ℕ) e)
        ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D) :
    Lindeberg.mean μ (crossIndG edge o n) *
        (1 - Lindeberg.mean μ (crossIndG edge o n)) / D ≤
      ∑ e, Lindeberg.cov μ (crossIndG edge o n) (Lindeberg.coord e) := by
  classical
  haveI : Nonempty (↥(Finset.Icc 1 n)) :=
    ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩⟩
  let f : ConfigSpace E → ℝ := crossIndG edge o n
  let T : ↥(Finset.Icc 1 n) → DecisionTree E := fun k =>
    crossTree endU endV o (vertexBoundary d n) l (disc₀ (k : ℕ))
  let R : ↥(Finset.Icc 1 n) → E → ℝ := fun k e =>
    boxRevealG μ edge endU endV (k : ℕ) e
  have hf : Monotone f :=
    (connectedToSet_increasing edge o (vertexBoundary d n)).indicator_monotone
  have hidem : ∀ ω, f ω * f ω = f ω := by
    intro ω
    unfold f crossIndG
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  have hT : ∀ k, (T k).evalR = f := by
    intro k
    funext ω
    have hk1 := (Finset.mem_Icc.mp k.2).1
    have hkn := (Finset.mem_Icc.mp k.2).2
    have heval := evalR_crossTree_connected (E := E) (d := d) hinj hcoh hadj
      (k : ℕ) n hk1 hkn o (ho (k : ℕ) hk1) l hl (disc₀ (k : ℕ))
      (hdisc₀sup (k : ℕ)) (hoB (k : ℕ)) ω
    unfold T f crossIndG
    rw [heval]
    by_cases hc : ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n)
    · have hm : ω ∈ crossEvent edge o (vertexBoundary d n) := hc
      rw [if_pos hc, Set.indicator_of_mem hm]
    · have hm : ω ∉ crossEvent edge o (vertexBoundary d n) := hc
      rw [if_neg hc, Set.indicator_of_notMem hm]
  have hreach : ∀ k e, revealmentMu μ (T k) e ≤ R k e := by
    intro k e
    unfold T R boxRevealG
    exact frf_mean_reveal_crossTree_le_connBox (μ := μ) (fun ω => (hpos ω).le)
      hinj hcoh hadj o (vertexBoundary d n) (k : ℕ) l (disc₀ (k : ℕ))
      (hdisc₀sub (k : ℕ)) e
  have havg := frf_avg_treeReveal_le_of_perScale T R D hreach hsum
  have hmain := var_le_avg_adaptive_reveal_mul_sum_cov_unconditional
    hpos hμ1 hFKG T hf hT D havg
  have hvar : Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) :=
    RevealmentBoundAssembly.var_eq_theta_one_sub_theta hidem
  rw [hvar] at hmain
  rw [div_le_iff₀ hD]
  simpa [f, mul_comm] using hmain




theorem hcov_lattice_mass
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List E) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n) (Λ : Finset (Site d)) (hne : Λ.Nonempty)
    (hLu : ∀ e : E, endU e ∈ Λ) (hLv : ∀ e : E, endV e ∈ Λ)
    (hUbox : ∀ e : E, endU e ∈ box d n)
    (hVbox : ∀ e : E, endV e ∈ box d n) :
    Lindeberg.mean μ (crossIndG edge o n) *
        (1 - Lindeberg.mean μ (crossIndG edge o n)) /
          (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
            Lindeberg.mean μ (fun ω =>
              if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
              then (1 : ℝ) else 0)) / (n : ℝ))
      ≤ ∑ e, Lindeberg.cov μ (crossIndG edge o n) (Lindeberg.coord e) := by
  classical
  let conn : Site d → ℕ → ℝ := fun x j => Lindeberg.mean μ (fun ω =>
    if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
    then (1 : ℝ) else 0)
  let M : ℝ := Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, conn x j)
  have hμ0 : ∀ ω, 0 ≤ μ ω := fun ω => (hpos ω).le
  have hconn0 : ∀ x j, 0 ≤ conn x j := fun x j => mean_indicator_nonneg hμ0 _
  have hMpos : 0 < M := by
    obtain ⟨x, hx⟩ := hne
    have hconnzero : conn x 0 = 1 := by
      have hall : (fun ω : ConfigSpace E =>
          if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x 0)
          then (1 : ℝ) else 0) = fun _ => 1 := by
        funext ω
        rw [if_pos]
        exact ⟨x, centeredRadius_self x, connected_refl _ _⟩
      change Lindeberg.mean μ (fun ω =>
        if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x 0)
        then (1 : ℝ) else 0) = 1
      rw [hall]
      exact Lindeberg.mean_const μ hμ1 1
    have hs : 1 ≤ ∑ j ∈ Finset.range n, conn x j := by
      rw [← hconnzero]
      apply Finset.single_le_sum (fun j _ => hconn0 x j)
      simp
      omega
    have := Finset.le_sup' (fun y => ∑ j ∈ Finset.range n, conn y j) hx
    linarith
  have hncard : (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) = (n : ℝ) := by
    rw [Fintype.card_coe, Nat.card_Icc]
    norm_num
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  let D : ℝ := 4 * M / (n : ℝ)
  have hDpos : 0 < D := by unfold D; positivity
  have hsum : ∀ e : E,
      (∑ k : ↥(Finset.Icc 1 n), boxRevealG μ edge endU endV (k : ℕ) e)
        ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D := by
    intro e
    have hu := revealment_sum_bound_lattice μ hμ0 edge Λ hne (endU e) (hLu e) (hUbox e)
    have hv := revealment_sum_bound_lattice μ hμ0 edge Λ hne (endV e) (hLv e) (hVbox e)
    have hsplit :
        (∑ k : ↥(Finset.Icc 1 n), boxRevealG μ edge endU endV (k : ℕ) e) =
          (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean μ (fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
            then (1 : ℝ) else 0)) +
          (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean μ (fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
            then (1 : ℝ) else 0)) := by
      rw [Finset.sum_coe_sort (Finset.Icc 1 n)
        (fun k => boxRevealG μ edge endU endV k e)]
      simp only [boxRevealG, Finset.sum_add_distrib]
    rw [hsplit, hncard]
    change _ ≤ (n : ℝ) * (4 * M / (n : ℝ))
    have : (n : ℝ) * (4 * M / (n : ℝ)) = 4 * M := by field_simp
    rw [this]
    change _ ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, conn x j)
    linarith
  have hmain := hcov_crossTree_mass μ hpos hμ1 hFKG hinj hcoh hadj o l hl disc₀
    hdisc₀sub hdisc₀sup hoB ho n hn D hDpos hsum
  simpa [conn, M, D] using hmain

variable {W : Type*} [Fintype W] [DecidableEq W]



theorem fk_q2_hcov_lattice
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {edge : Sym2 W → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : Sym2 W → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List (Sym2 W)) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Finset (Site d)) (hne : Λ.Nonempty)
    (hLu : ∀ e : Sym2 W, endU e ∈ Λ) (hLv : ∀ e : Sym2 W, endV e ∈ Λ)
    (hUbox : ∀ e : Sym2 W, endU e ∈ box d n)
    (hVbox : ∀ e : Sym2 W, endV e ∈ box d n) :
    Lindeberg.mean (fkMass G p 2) (crossInd edge o n)
        * (1 - Lindeberg.mean (fkMass G p 2) (crossInd edge o n))
        / (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
            Lindeberg.mean (fkMass G p 2) (fun ω =>
              if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
              then (1 : ℝ) else 0)) / (n : ℝ))
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (crossInd edge o n) (Lindeberg.coord e) := by
  classical
  let μ : ConfigSpace (Sym2 W) → ℝ := fkMass G p 2
  let conn : Site d → ℕ → ℝ := fun x j =>
    Lindeberg.mean μ (fun ω =>
      if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
      then (1 : ℝ) else 0)
  let M : ℝ := Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, conn x j)
  have hμ0 : ∀ ω, 0 ≤ μ ω := fun ω => (fkMass_pos G hp hp1 (by norm_num) ω).le
  have hconn0 : ∀ x j, 0 ≤ conn x j := fun x j => mean_indicator_nonneg hμ0 _
  have hMpos : 0 < M := by
    obtain ⟨x, hx⟩ := hne
    have hconnzero : conn x 0 = 1 := by
      have hall : (fun ω : ConfigSpace (Sym2 W) =>
          if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x 0)
          then (1 : ℝ) else 0) = fun _ => 1 := by
        funext ω
        rw [if_pos]
        exact ⟨x, centeredRadius_self x, connected_refl _ _⟩
      change Lindeberg.mean μ (fun ω =>
        if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x 0)
        then (1 : ℝ) else 0) = 1
      rw [hall]
      exact Lindeberg.mean_const μ (fkMass_sum_eq_one G hp hp1 (by norm_num)) 1
    have hsum : 1 ≤ ∑ j ∈ Finset.range n, conn x j := by
      rw [← hconnzero]
      apply Finset.single_le_sum (fun j _ => hconn0 x j)
      simp
      omega
    have hsup : (∑ j ∈ Finset.range n, conn x j) ≤ M := by
      exact Finset.le_sup' (fun y => ∑ j ∈ Finset.range n, conn y j) hx
    linarith
  have hncard : (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) = (n : ℝ) := by
    rw [Fintype.card_coe, Nat.card_Icc]
    norm_num
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  let D : ℝ := 4 * M / (n : ℝ)
  have hDpos : 0 < D := by unfold D; positivity
  have hsum : ∀ e : Sym2 W,
      (∑ k : ↥(Finset.Icc 1 n), boxReveal μ edge endU endV (k : ℕ) e)
        ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D := by
    intro e
    have hu := revealment_sum_bound_lattice μ hμ0 edge Λ hne (endU e) (hLu e) (hUbox e)
    have hv := revealment_sum_bound_lattice μ hμ0 edge Λ hne (endV e) (hLv e) (hVbox e)
    have hsplit :
        (∑ k : ↥(Finset.Icc 1 n), boxReveal μ edge endU endV (k : ℕ) e) =
          (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean μ (fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
            then (1 : ℝ) else 0))
          + (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean μ (fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
            then (1 : ℝ) else 0)) := by
      rw [Finset.sum_coe_sort (Finset.Icc 1 n)
        (fun k => boxReveal μ edge endU endV k e)]
      simp only [boxReveal, Finset.sum_add_distrib]
    rw [hsplit, hncard]
    change _ ≤ (n : ℝ) * (4 * M / (n : ℝ))
    have hright : (n : ℝ) * (4 * M / (n : ℝ)) = 4 * M := by field_simp
    rw [hright]
    change _ ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, conn x j)
    linarith
  have hsum' : ∀ e : Sym2 W,
      (∑ k : ↥(Finset.Icc 1 n), boxReveal (fkMass G p 2) edge endU endV (k : ℕ) e)
        ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D := by
    simpa [μ] using hsum
  have hmain := acl_fk_q2_hcov_crossTree G hp hp1 hinj hcoh hadj o l hl disc₀
    hdisc₀sub hdisc₀sup hoB ho n hn D hDpos hsum'
  change _ ≤ _
  simpa [μ, conn, M, D] using hmain

end AdaptiveCovLowerGeom
end OSSS
end StatMech
