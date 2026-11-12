/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Code.OSSS.IntegrationSubcriticalAssembly
import Code.OSSS.SharpnessFK
import Code.OSSS.Integration

open scoped BigOperators
open Real Filter Topology Set Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS.IntegrationSubcritical









noncomputable def osd_Sigma (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, f k x


theorem osd_Sigma_eq_Sig (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) :
    osd_Sigma f n x = StatMech.OSSS.IntegrationSubcritical.Sig f n x := rfl





























theorem osd_two_stage_decay (f f' : ℕ → ℝ → ℝ) (α δ β M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1) (hMnn : 0 ≤ M) (hN : 1 ≤ N)
    (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (f n) (f' n x) x)
    (hfnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ f n x)
    (hfM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, f n x ≤ M)
    (hfmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β →
      y ≤ x → f k y ≤ f k x)
    (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < osd_Sigma f n x)
    (hdiff : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β,
      ((n : ℝ) / osd_Sigma f n x) * f n x ≤ f' n x)
    (hSpoly : ∀ n : ℕ, N ≤ n → osd_Sigma f n β ≤ (n : ℝ) ^ (1 - α)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n →
      f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) :=
  
  
  
  StatMech.OSSS.IntegrationSubcritical.isc_subcritical_decay
    f f' α δ β M N hδ hα hα1 hMnn hN hd hfnn hfM hfmono hSpos hdiff hSpoly








theorem osd_gronwall_lower_is_dep (a b lam : ℝ) (hab : a ≤ b) (g g' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hineq : ∀ x ∈ Icc a b, lam * g x ≤ g' x) :
    Real.exp (lam * (b - a)) * g a ≤ g b :=
  StatMech.OSSS.SharpnessFK.gronwall_lower a b lam hab g g' hd hineq




theorem osd_stage1_stretched (f f' : ℕ → ℝ → ℝ) (n : ℕ) (α δ β M : ℝ)
    (hn : 1 ≤ n) (hδ : 0 < δ)
    (hd : ∀ x ∈ Icc (β - δ) β, HasDerivAt (f n) (f' n x) x)
    (hfnn : ∀ x ∈ Icc (β - δ) β, 0 ≤ f n x)
    (hSpos : ∀ x ∈ Icc (β - δ) β, 0 < osd_Sigma f n x)
    (hSpoly : ∀ x ∈ Icc (β - δ) β, osd_Sigma f n x ≤ (n : ℝ) ^ (1 - α))
    (hdiff : ∀ x ∈ Icc (β - δ) β, ((n : ℝ) / osd_Sigma f n x) * f n x ≤ f' n x)
    (hfb : f n β ≤ M) :
    f n (β - δ) ≤ M * Real.exp (-(δ * (n : ℝ) ^ α)) :=
  StatMech.OSSS.IntegrationSubcritical.isc_stretched_decay
    f f' n α δ β M hn hδ hd hfnn hSpos hSpoly hdiff hfb



theorem osd_stage2_exponential (f f' : ℕ → ℝ → ℝ) (n : ℕ) (δ Q β M : ℝ)
    (hδ : 0 < δ) (hQ : 0 < Q)
    (hd : ∀ x ∈ Icc (β - 2 * δ) (β - δ), HasDerivAt (f n) (f' n x) x)
    (hfnn : ∀ x ∈ Icc (β - 2 * δ) (β - δ), 0 ≤ f n x)
    (hSpos : ∀ x ∈ Icc (β - 2 * δ) (β - δ), 0 < osd_Sigma f n x)
    (hSle : ∀ x ∈ Icc (β - 2 * δ) (β - δ), osd_Sigma f n x ≤ Q)
    (hdiff : ∀ x ∈ Icc (β - 2 * δ) (β - δ), ((n : ℝ) / osd_Sigma f n x) * f n x ≤ f' n x)
    (hfb : f n (β - δ) ≤ M) :
    f n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) :=
  StatMech.OSSS.IntegrationSubcritical.isc_stage2_decay
    f f' n δ Q β M hδ hQ hd hfnn hSpos hSle hdiff hfb

end Walls
end StatMech
