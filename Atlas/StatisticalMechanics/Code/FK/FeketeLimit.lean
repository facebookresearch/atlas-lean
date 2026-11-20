/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.FK.IVPressureConvex

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice
















theorem fkl_tendsto_div_of_subadditive (u : ℕ → ℝ) (hsub : Subadditive u)
    (hbdd : BddBelow (Set.range fun n => u n / n))
    (e : ℕ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (he : Tendsto (fun n => e n / n) atTop (𝓝 c)) :
    Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / c)) := by
  have hu : Tendsto (fun n => u n / n) atTop (𝓝 hsub.lim) := hsub.tendsto_lim hbdd
  have hdiv : Tendsto (fun n => (u n / n) / (e n / n)) atTop (𝓝 (hsub.lim / c)) :=
    hu.div he hc
  refine hdiv.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp








variable {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
  (Gn : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (Gn n).Adj]























theorem fkl_tiltFreeEnergy_tendsto (q : ℝ) (hq : 0 < q) (t : ℝ)
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hsuper : Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q)))
    (hbdd : BddBelow (Set.range fun n =>
      (- Real.log (fkZ (Gn n) (fsc_logistic t) q)) / n))
    (c : ℝ) (hc : c ≠ 0)
    (he : Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop
      (𝓝 (- (hsuper.lim / c) + Real.log (1 + Real.exp t))) := by
  set u : ℕ → ℝ := fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q) with hu
  set e : ℕ → ℝ := fun n => ((Gn n).edgeFinset.card : ℝ) with hedef
  
  have hratio : Tendsto (fun n => u n / e n) atTop (𝓝 (hsuper.lim / c)) :=
    fkl_tendsto_div_of_subadditive u hsuper hbdd e c hc he
  
  have hform : (fun n => ivp2_tiltFreeEnergy (Gn n) q t)
      = fun n => - (u n / e n) + Real.log (1 + Real.exp t) := by
    funext n
    unfold ivp2_tiltFreeEnergy
    have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
    have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
    have hZ : 0 < fkZ (Gn n) (fsc_logistic t) q := fkZ_pos (Gn n) hp0 hp1 hq
    have hEne : ((Gn n).edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast (hE n).ne'
    simp only [hu, hedef]
    field_simp
  rw [hform]
  
  have hneg : Tendsto (fun n => - (u n / e n)) atTop (𝓝 (- (hsuper.lim / c))) :=
    hratio.neg
  simpa using hneg.add_const (Real.log (1 + Real.exp t))
































theorem fkl_fekete_limit (q : ℝ) (hq : 0 < q)
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hsuper : ∀ t, Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q)))
    (hbdd : ∀ t, BddBelow (Set.range fun n =>
      (- Real.log (fkZ (Gn n) (fsc_logistic t) q)) / n))
    (c : ℝ → ℝ) (hc : ∀ t, c t ≠ 0)
    (he : ∀ t, Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 (c t))) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ univ g := by
  
  classical
  refine ⟨fun t => - ((hsuper t).lim / c t) + Real.log (1 + Real.exp t), ?_, ?_⟩
  · intro t
    exact fkl_tiltFreeEnergy_tendsto Gn q hq t hE (hsuper t) (hbdd t) (c t) (hc t) (he t)
  · 
    refine ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
      (fun n => ivp2_tiltFreeEnergy (Gn n) q)
      (fun t => - ((hsuper t).lim / c t) + Real.log (1 + Real.exp t)) ?_ ?_
    · exact fun n => ivp2_tiltFreeEnergy_convexOn (Gn n) q hq (hE n)
    · intro t
      exact fkl_tiltFreeEnergy_tendsto Gn q hq t hE (hsuper t) (hbdd t) (c t) (hc t) (he t)











theorem fkl_subadditive_zero : Subadditive (fun _ : ℕ => (0:ℝ)) := by
  intro m n; simp








theorem fkl_superMultiplicative_satisfiable :
    ∃ (u : ℕ → ℝ) (hsub : Subadditive u) (e : ℕ → ℝ) (c : ℝ),
      c ≠ 0 ∧ BddBelow (Set.range fun n => u n / n)
        ∧ Tendsto (fun n => e n / n) atTop (𝓝 c)
        ∧ Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / c)) := by
  refine ⟨fun _ => (0:ℝ), fkl_subadditive_zero, fun n => (n:ℝ), 1, one_ne_zero, ?_, ?_, ?_⟩
  · exact ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℝ)))
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  · exact fkl_tendsto_div_of_subadditive _ fkl_subadditive_zero ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
      (fun n => (n:ℝ)) 1 one_ne_zero
      (by
        refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℝ)))
        filter_upwards [eventually_ne_atTop 0] with n hn
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        field_simp)

end FK

end StatMech
