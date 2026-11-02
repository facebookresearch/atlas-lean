/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.IVPressureConvex

/-!
# Free-energy limits from near-subadditivity in the box index

Fekete's lemma with an `o(n)` correction: if `u n + c n` is subadditive and `c n / n → 0`, then
`u n / n` converges; applied to `-log Z` of the boxes `Λ_n` for the `q = 2` model.

## i. Overview

Mathlib's `Subadditive.tendsto_lim` gives convergence of `(u n + c n)/n`; the correction `c n / n`
vanishes, so `u n / n` has the same limit, and dividing by an edge count `e n` with `e n / n → κ ≠
0`
gives the per-edge limit. `bfd_FKInterfaceData d t` packages these hypotheses for
`u n = -log Z_{Λ_n}(logistic(t), 2)` and `e n = |E(Λ_n)|`. It requires `|E(Λ_n)| / n` to converge to
a
finite nonzero `κ`, which holds only for `d = 1` (for `d ≥ 2`, `|E(Λ_n)| / n → ∞`), so the
predicate cannot hold for `d ≥ 2`. `bfd_fkInterfaceData_satisfiable` exhibits sequences
satisfying the abstract numeric hypotheses, not the box predicate.

## ii. Key results

- `bfd_tendsto_div_of_nearSubadditive` : Fekete's lemma with an `o(n)` correction.

## iii. Table of contents

- A. Fekete's lemma with a correction
- B. Box free energies

## iv. References

- M. Fekete, *Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit
  ganzzahligen Koeffizienten*, Math. Z. 17 (1923).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.58.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

/-! ## A. Fekete's lemma with a correction -/

/-- Fekete's lemma with an `o(n)` correction: if `u n + c n` is subadditive and bounded below after
dividing by `n`, and `c n / n → 0`, then `u n / n` converges. See also Mathlib's
`Subadditive.tendsto_lim`.
-/
lemma bfd_tendsto_div_of_nearSubadditive (u c : ℕ → ℝ)
    (hsub : Subadditive (fun n => u n + c n))
    (hbdd : BddBelow (Set.range fun n => (u n + c n) / n))
    (hc : Tendsto (fun n => c n / n) atTop (𝓝 0)) :
    Tendsto (fun n => u n / n) atTop (𝓝 hsub.lim) := by
  have hw : Tendsto (fun n => (u n + c n) / n) atTop (𝓝 hsub.lim) := hsub.tendsto_lim hbdd
  have hsplit : (fun n => u n / n) = fun n => (u n + c n) / n - c n / n := by
    funext n; rw [add_div]; ring
  rw [hsplit]
  simpa using hw.sub hc

lemma bfd_tendsto_perEdge_of_nearSubadditive (u c : ℕ → ℝ)
    (hsub : Subadditive (fun n => u n + c n))
    (hbdd : BddBelow (Set.range fun n => (u n + c n) / n))
    (hc : Tendsto (fun n => c n / n) atTop (𝓝 0))
    (e : ℕ → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (he : Tendsto (fun n => e n / n) atTop (𝓝 κ)) :
    Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / κ)) := by
  have hun : Tendsto (fun n => u n / n) atTop (𝓝 hsub.lim) :=
    bfd_tendsto_div_of_nearSubadditive u c hsub hbdd hc
  have hdiv : Tendsto (fun n => (u n / n) / (e n / n)) atTop (𝓝 (hsub.lim / κ)) := hun.div he hκ
  refine hdiv.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

variable {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
  (Gn : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (Gn n).Adj]

lemma bfd_tiltFreeEnergy_tendsto_of_nearSubadditive (q : ℝ) (hq : 0 < q) (t : ℝ)
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (c : ℕ → ℝ)
    (hsub : Subadditive (fun n => -Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n))
    (hbdd : BddBelow (Set.range fun n =>
      (-Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n) / n))
    (hc : Tendsto (fun n => c n / n) atTop (𝓝 0))
    (κ : ℝ) (hκ : κ ≠ 0)
    (he : Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop
      (𝓝 (- (hsub.lim / κ) + Real.log (1 + Real.exp t))) := by
  set u : ℕ → ℝ := fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q) with hu
  set e : ℕ → ℝ := fun n => ((Gn n).edgeFinset.card : ℝ) with hedef
  have hratio : Tendsto (fun n => u n / e n) atTop (𝓝 (hsub.lim / κ)) :=
    bfd_tendsto_perEdge_of_nearSubadditive u c hsub hbdd hc e κ hκ he
  have hform : (fun n => ivp2_tiltFreeEnergy (Gn n) q t)
      = fun n => - (u n / e n) + Real.log (1 + Real.exp t) := by
    funext n
    unfold ivp2_tiltFreeEnergy
    have hp0 : (0 : ℝ) < fsc_logistic t := fsc_logistic_pos t
    have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
    have hZ : 0 < fkZ (Gn n) (fsc_logistic t) q := fkZ_pos (Gn n) hp0 hp1 hq
    have hEne : ((Gn n).edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast (hE n).ne'
    simp only [hu, hedef]
    field_simp
  rw [hform]
  have hneg : Tendsto (fun n => - (u n / e n)) atTop (𝓝 (- (hsub.lim / κ))) := hratio.neg
  simpa using hneg.add_const (Real.log (1 + Real.exp t))

variable {d : ℕ}

/-! ## B. Box free energies -/

/-- Near-subadditivity of `n ↦ -log Z_{Λ_n}(logistic(t), 2)` with an `o(n)` correction, together
with
`|E(Λ_n)| / n → κ ≠ 0`. The last condition fails for `d ≥ 2`, so this predicate can hold only
for
`d = 1`.
-/
def bfd_FKInterfaceData (d : ℕ) (t : ℝ) : Prop :=
  ∃ (c : ℕ → ℝ) (κ : ℝ),
    Subadditive (fun n => - Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + c n)
    ∧ BddBelow (Set.range fun n =>
        (- Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + c n) / n)
    ∧ Tendsto (fun n => c n / n) atTop (𝓝 0)
    ∧ κ ≠ 0
    ∧ Tendsto (fun n => ((boxGraph d n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ)

lemma bfd_fkInterfaceData_satisfiable :
    ∃ (u c : ℕ → ℝ) (e : ℕ → ℝ) (κ : ℝ),
      Subadditive (fun n => u n + c n)
      ∧ BddBelow (Set.range fun n => (u n + c n) / n)
      ∧ Tendsto (fun n => c n / n) atTop (𝓝 0)
      ∧ κ ≠ 0
      ∧ Tendsto (fun n => e n / n) atTop (𝓝 κ) := by
  refine ⟨fun _ => 0, fun _ => 0, fun n => (n : ℝ), 1, ?_, ?_, ?_, one_ne_zero, ?_⟩
  · intro m n; simp
  · exact ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
  · simp only [zero_div]; exact tendsto_const_nhds
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)))
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

end FK

end StatMech
