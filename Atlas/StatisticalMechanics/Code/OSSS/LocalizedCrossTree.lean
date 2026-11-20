/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.OSSS.DecisionTreeReindex
import Code.OSSS.FamilyEqzzzResolution
import Code.OSSS.RevealmentCrossBox
import Code.OSSS.ReachBoxCrossing
import Code.OSSS.RevealmentTranslation

open scoped BigOperators

namespace StatMech
namespace OSSS
namespace LocalizedCrossTree

open DecisionTree LindebergTree Lindeberg
open RevealmentConstruction FamilyEqzzzResolution ReachBoxCrossing
open RevealmentTranslation
open Lattice
open scoped Classical

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
variable {d : Nat}



noncomputable def localizedBoxReveal (mu : ConfigSpace E -> Real) (iota : I -> E)
    (edge : I -> Sym2 (Site d)) (endU endV : I -> Site d)
    (k : Nat) (i : I) : Real :=
  mean mu (fun omega => if ConnectedToSet d
      (liftCfg edge (restrictConfig iota omega)) (endU i) (vertexBoundary d k)
    then (1 : Real) else 0)
  + mean mu (fun omega => if ConnectedToSet d
      (liftCfg edge (restrictConfig iota omega)) (endV i) (vertexBoundary d k)
    then (1 : Real) else 0)




theorem revealment_sum_bound_lattice_map
    (mu : ConfigSpace E -> Real) (hmu0 : forall omega, 0 <= mu omega)
    (cfg : ConfigSpace E -> ConfigSpace I) (edge : I -> Sym2 (Site d))
    (Lambda : Finset (Site d)) (hne : Lambda.Nonempty)
    (u : Site d) (hu : u ∈ Lambda) (hubox : u ∈ box d n) :
    (∑ k ∈ Finset.Icc 1 n,
      mean mu (fun omega => if ConnectedToSet d (liftCfg edge (cfg omega)) u
        (vertexBoundary d k) then (1 : Real) else 0)) <=
      2 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n,
        mean mu (fun omega => if ConnectedToSet d (liftCfg edge (cfg omega)) x
          (centeredBoundary x j) then (1 : Real) else 0)) := by
  classical
  let conn : Site d -> Nat -> Real := fun x j =>
    mean mu (fun omega => if ConnectedToSet d (liftCfg edge (cfg omega)) x
      (centeredBoundary x j) then (1 : Real) else 0)
  let qf : Nat -> Real := fun k =>
    mean mu (fun omega => if ConnectedToSet d (liftCfg edge (cfg omega)) u
      (vertexBoundary d k) then (1 : Real) else 0)
  have hconn0 : forall x j, 0 <= conn x j := fun x j =>
    RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hrn : siteRadius u <= n := mem_box_iff_siteRadius_le.mp hubox
  change (∑ k ∈ Finset.Icc 1 n, qf k) <=
    2 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n, conn x j)
  by_cases hr0 : siteRadius u = 0
  · have hcomp0 : forall k, 1 <= k -> qf k <= conn u (k - 1) := by
      intro k hk
      apply mean_indicator_mono hmu0
      intro omega homega
      have hm : k - 1 <= ((k : Int) - (siteRadius u : Int)).natAbs := by
        rw [hr0]
        simp
      exact connectedToSet_originBoundary_imp_centered_of_le hm homega
    have hsum : (∑ k ∈ Finset.Icc 1 n, qf k) <=
        ∑ j ∈ Finset.range n, conn u j := by
      calc
        (∑ k ∈ Finset.Icc 1 n, qf k) <=
            ∑ k ∈ Finset.Icc 1 n, conn u (k - 1) :=
          Finset.sum_le_sum (fun k hk => hcomp0 k (Finset.mem_Icc.mp hk).1)
        _ = ∑ j ∈ Finset.range n, conn u j :=
          sum_Icc_one_pred_eq_sum_range (conn u) n
    have hsum0 : 0 <= ∑ j ∈ Finset.range n, conn u j :=
      Finset.sum_nonneg (fun j _ => hconn0 u j)
    have hsup : 2 * (∑ j ∈ Finset.range n, conn u j) <=
        2 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n, conn x j) :=
      sum_le_two_mul_sup' Lambda hne
        (fun x => ∑ j ∈ Finset.range n, conn x j) u hu
    exact hsum.trans ((show (∑ j ∈ Finset.range n, conn u j) <=
      2 * (∑ j ∈ Finset.range n, conn u j) by linarith).trans hsup)
  · have hr1 : 1 <= siteRadius u := Nat.one_le_iff_ne_zero.mpr hr0
    apply revealment_sum_bound_range Lambda hne conn hconn0 n (siteRadius u)
      hr1 hrn u hu qf
    intro k
    apply mean_indicator_mono hmu0
    intro omega homega
    exact connectedToSet_originBoundary_imp_centered homega




theorem hcov_reindexed_crossTree_mass
    (mu : ConfigSpace E -> Real) (hpos : forall omega, 0 < mu omega)
    (hmu1 : ∑ omega, mu omega = 1) (hFKG : FKGLatticeCondition mu)
    (iota : I -> E) (hiota : Function.Injective iota)
    {edge : I -> Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : I -> Site d} (hcoh : forall i, edge i = s(endU i, endV i))
    (hadj : forall i, (hypercubicLattice d).Adj (endU i) (endV i))
    (o : Site d) (l : List I) (hl : forall i, i ∈ l)
    (disc0 : Nat -> Finset (Site d))
    (hdisc0sub : ∀ k x, x ∈ disc0 k → x ∈ vertexBoundary d k)
    (n : Nat) (hn : 1 <= n)
    (f : ConfigSpace E -> Real) (hf : Monotone f)
    (hidem : forall omega, f omega * f omega = f omega)
    (hcompute : forall (k : ↑(Finset.Icc 1 n)) (omega : ConfigSpace E),
      (crossTree endU endV o (vertexBoundary d n) l (disc0 (k : Nat))).evalR
          (restrictConfig iota omega) = f omega)
    (D : Real) (hD : 0 < D)
    (hsum : forall i : I,
      (∑ k : ↑(Finset.Icc 1 n),
        localizedBoxReveal mu iota edge endU endV (k : Nat) i)
        <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) / D <=
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
  classical
  haveI : Nonempty (↑(Finset.Icc 1 n)) :=
    ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩⟩
  let Tinner : ↑(Finset.Icc 1 n) -> DecisionTree I := fun k =>
    crossTree endU endV o (vertexBoundary d n) l (disc0 (k : Nat))
  let T : ↑(Finset.Icc 1 n) -> DecisionTree E := fun k =>
    (Tinner k).reindex iota
  have hT : forall k, (T k).evalR = f := by
    intro k
    funext omega
    simpa [T] using hcompute k omega
  have hmu0 : forall omega, 0 <= mu omega := fun omega => (hpos omega).le
  have hreachImage : forall k i,
      revealmentMu mu (T k) (iota i) <=
        localizedBoxReveal mu iota edge endU endV (k : Nat) i := by
    intro k i
    unfold revealmentMu localizedBoxReveal
    refine (mean_indicator_mono hmu0 _ _ ?_).trans (mean_indicator_or_le hmu0 _ _)
    intro omega hquery
    have hqueryInner : i ∈ (Tinner k).queried (restrictConfig iota omega) := by
      apply (mem_queried_reindex_iff iota hiota (Tinner k) omega i).mp
      simpa [T] using hquery
    have hor := queried_crossTree_imp endU endV o (vertexBoundary d (k : Nat))
      (vertexBoundary d n) l (disc0 (k : Nat)) (hdisc0sub (k : Nat))
      (restrictConfig iota omega) i hqueryInner
    rcases hor with hu | hv
    · exact Or.inl (connOpenSet_imp_connectedToSet hinj hcoh hadj hu)
    · exact Or.inr (connOpenSet_imp_connectedToSet hinj hcoh hadj hv)
  have hcardpos : (0 : Real) < Fintype.card (↑(Finset.Icc 1 n)) := by
    exact_mod_cast Fintype.card_pos
  have havg : forall e,
      (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
        ∑ k, revealmentMu mu (T k) e <= D := by
    intro e
    by_cases he : e ∈ Set.range iota
    · obtain ⟨i, rfl⟩ := he
      have hs : (∑ k, revealmentMu mu (T k) (iota i)) <=
          ∑ k : ↑(Finset.Icc 1 n),
            localizedBoxReveal mu iota edge endU endV (k : Nat) i :=
        Finset.sum_le_sum fun k _ => hreachImage k i
      have hb := hs.trans (hsum i)
      calc
        (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
            ∑ k, revealmentMu mu (T k) (iota i)
            <= (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
              ((Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) := by
                gcongr
        _ = D := by field_simp
    · have hz : forall k, revealmentMu mu (T k) e = 0 := by
        intro k
        unfold revealmentMu mean
        apply Finset.sum_eq_zero
        intro omega _
        change (if e ∈ (T k).queried omega then (1 : Real) else 0) * mu omega = 0
        rw [if_neg]
        · ring
        · exact not_mem_queried_reindex_of_not_range iota (Tinner k) omega e he
      simp_rw [hz]
      simpa using hD.le
  have hmain := var_le_avg_adaptive_reveal_mul_sum_cov_unconditional
    hpos hmu1 hFKG T hf hT D havg
  have hvar : Lindeberg.var mu f =
      Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) :=
    RevealmentBoundAssembly.var_eq_theta_one_sub_theta hidem
  rw [hvar] at hmain
  exact (div_le_iff₀ hD).2 (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmain)

end LocalizedCrossTree
end OSSS
end StatMech
