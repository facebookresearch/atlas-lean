/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Berkson's bias: selection into hospital creates spurious associations

Diseases indexed by a finite type occur independently, disease `i` with incidence
`p_i ∈ (0, 1)`. Each disease independently brings its bearer to hospital with selective
probability `s_i = 1 - t_i`, so a person whose set of diseases is `S` is admitted with
probability `f_S = 1 - t₀ ∏_{i ∈ S} t_i`. Berkson's model has `t₀ = 1`: a person with none of the
diseases is never admitted. Allowing `t₀ ∈ (0, 1]` admits people without any of the diseases at
rate `1 - t₀`.

Among admitted persons, two diseases that are independent in the population become negatively
associated. The ratio of multiple to single diagnoses is inflated: with equal small selective
rates, about twice for two diagnoses and about three times for three. A comparison of the
frequency of a third disease between two diagnostic groups can show a spurious difference of
either sign, depending on the selective rates (Berkson's Tables 7 and 9). The comparison is valid
when the compared disease has selective rate zero, or when each group consists of one disease
and the two selective rates are equal.

Berkson displays the closed forms as formulas; the statements below follow from his stated model
and reproduce the tabulated numbers.

Sources: J. Berkson, "Limitations of the application of fourfold table analysis to hospital
data", Biometrics Bull. 2 (1946) 47–53; reprinted Int. J. Epidemiol. 43 (2014) 511–515.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.StatisticalGenetics.BerksonBias
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.BerksonBiasWanted

open Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The population probability `∏_{i ∈ S} p_i ∏_{i ∉ S} (1 - p_i)` that the set of diseases of a
person is exactly `S`. -/
def diseaseSetProb (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, (1 - p i)

/-- The admission probability `f_S = 1 - t₀ ∏_{i ∈ S} t_i` of a person whose set of diseases is
`S`. -/
def admissionProb (t₀ : ℝ) (t : ι → ℝ) (S : Finset ι) : ℝ :=
  1 - t₀ * ∏ i ∈ S, t i

/-- The hospital mass `P(diseases = S, admitted) = P(S) f_S`. -/
def hospitalMass (p : ι → ℝ) (t₀ : ℝ) (t : ι → ℝ) (S : Finset ι) : ℝ :=
  diseaseSetProb p S * admissionProb t₀ t S

/-- The frequency of disease `c` among admitted persons whose disease set satisfies `G`:
`∑_{S ∈ G, c ∈ S} P(S, admitted) / ∑_{S ∈ G} P(S, admitted)`. It is meaningful when the group has
positive admitted mass; if that mass is `0`, Lean's convention `x / 0 = 0` makes the value `0`. -/
noncomputable def hospitalFrequency (p : ι → ℝ) (t₀ : ℝ) (t : ι → ℝ) (G : Finset ι → Prop)
    [DecidablePred G] (c : ι) : ℝ :=
  (∑ S ∈ Finset.univ.filter (fun S => G S ∧ c ∈ S), hospitalMass p t₀ t S) /
    ∑ S ∈ Finset.univ.filter G, hospitalMass p t₀ t S

/-- **Admitted persons with multiple diagnoses are over-represented** (Berkson 1946). For a
common probability `t ∈ [0, 1)` of not triggering admission (selective rate `1 - t`) and `t₀ = 1`,
`f_2 / f_1 = (1 - t²) / (1 - t) = 1 + t` and `f_3 / f_1 = (1 - t³) / (1 - t) = 1 + t + t²`;
as the selective rate tends to `0` (`t → 1⁻`) these ratios tend to `2` and `3`.

Source: Berkson (1946), on the ratio of multiple to single diagnoses being "about twice" and
"about three times"; the exact ratios follow from the selection model. -/
public theorem_wanted admission_ratios :
    (∀ t : ℝ, 0 ≤ t → t < 1 →
      (1 - t ^ 2) / (1 - t) = 1 + t ∧ (1 - t ^ 3) / (1 - t) = 1 + t + t ^ 2) ∧
    Tendsto (fun t : ℝ => (1 - t ^ 2) / (1 - t)) (𝓝[<] 1) (𝓝 2) ∧
    Tendsto (fun t : ℝ => (1 - t ^ 3) / (1 - t)) (𝓝[<] 1) (𝓝 3)

/-- **Berkson's inequality** (Berkson 1946). Under the independent population disease law
(`diseaseSetProb`), let the diseases occur independently with incidences `p_i ∈ (0, 1)` and
probabilities `t_i ∈ [0, 1]` of not triggering admission, let `t₀ ∈ (0, 1]`, and let `a ≠ b` be
two diseases with `t_a < 1` and `t_b < 1` (each raises the admission probability). Then among
admitted persons, disease `a` is strictly less frequent among those with disease `b` than among
those without it: `hospitalFrequency (b ∈ S) a < hospitalFrequency (b ∉ S) a`.

Source: Berkson (1946); derived from his selection model. -/
public theorem_wanted hospitalFrequency_lt (p t : ι → ℝ) (t₀ : ℝ) (hp0 : ∀ i, 0 < p i)
    (hp1 : ∀ i, p i < 1) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (ht₀ : 0 < t₀)
    (ht₀' : t₀ ≤ 1) (a b : ι) (hab : a ≠ b) (ha : t a < 1) (hb : t b < 1) :
    hospitalFrequency p t₀ t (fun S => b ∈ S) a < hospitalFrequency p t₀ t (fun S => b ∉ S) a

/-- **The spurious difference can have either sign** (Berkson 1946, Tables 7 and 9). Take three
diseases, cholecystitis `0`, diabetes `1` and refractive errors `2`, with incidences
`p = (0.03, 0.01, 0.1)` and `t₀ = 1`. Compare the frequency of cholecystitis among admitted
diabetics with its frequency among admitted persons with refractive errors and no diabetes.
With equal selective rates `s = (0.05, 0.05, 0.05)` it is lower among the diabetics (Table 7:
about 5.45% against 5.69%). With `s = (0.15, 0.05, 0.20)` it is higher (Table 9: about 8.55%
against 4.72%). In the population the frequency is 3% in both groups.

Source: Berkson (1946), Tables 5, 7 and 9. -/
public theorem_wanted hospitalFrequency_tables :
    hospitalFrequency ![0.03, 0.01, 0.1] 1 ![0.95, 0.95, 0.95] (fun S => 1 ∈ S) 0 <
        hospitalFrequency ![0.03, 0.01, 0.1] 1 ![0.95, 0.95, 0.95] (fun S => 2 ∈ S ∧ 1 ∉ S) 0 ∧
      hospitalFrequency ![0.03, 0.01, 0.1] 1 ![0.85, 0.95, 0.80] (fun S => 2 ∈ S ∧ 1 ∉ S) 0 <
        hospitalFrequency ![0.03, 0.01, 0.1] 1 ![0.85, 0.95, 0.80] (fun S => 1 ∈ S) 0

/-- **A disease with selective rate zero is compared validly** (Berkson 1946). Under the
independent population disease law (`diseaseSetProb`), let the diseases occur independently with
incidences `p_i ∈ (0, 1)` and probabilities `t_i ∈ [0, 1]` of not triggering admission, let
`t₀ ∈ (0, 1]`, and let disease `c` have selective rate zero, `t_c = 1`. For a diagnostic group
given by a predicate `G` on the other diseases, `S ∈ group ↔ G (S.erase c)`, with positive
admitted mass, the frequency of `c` among admitted members of the group is its population
incidence `p_c`.

Source: Berkson (1946), comment on valid comparisons. -/
public theorem_wanted hospitalFrequency_eq_of_rate_zero (p t : ι → ℝ) (t₀ : ℝ)
    (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1) (c : ι) (hc : t c = 1) (G : Finset ι → Prop) [DecidablePred G]
    (hpos : 0 < ∑ S ∈ Finset.univ.filter (fun S => G (S.erase c)), hospitalMass p t₀ t S) :
    hospitalFrequency p t₀ t (fun S => G (S.erase c)) c = p c

/-- **Single-disease groups with equal selective rates are compared validly** (Berkson 1946). Under
the independent population disease law (`diseaseSetProb`), let the diseases occur independently
with incidences `p_i ∈ (0, 1)` and probabilities `t_i ∈ [0, 1]` of not triggering admission, let
`t₀ ∈ (0, 1]`, and let `c`, `d`, `r` be three distinct diseases with `t_d = t_r`. Suppose both
groups have positive admitted mass: the admitted persons whose diseases other than `c` are
exactly `{d}`, and those whose diseases other than `c` are exactly `{r}`. Then the frequency of
`c` among the first group equals its frequency among the second.

Source: Berkson (1946), comment on valid comparisons. -/
public theorem_wanted hospitalFrequency_eq_of_equal_rates (p t : ι → ℝ) (t₀ : ℝ)
    (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1) (c d r : ι) (hcd : c ≠ d) (hcr : c ≠ r) (hdr : d ≠ r)
    (heq : t d = t r)
    (hposd : 0 < ∑ S ∈ Finset.univ.filter (fun S => S.erase c = {d}), hospitalMass p t₀ t S)
    (hposr : 0 < ∑ S ∈ Finset.univ.filter (fun S => S.erase c = {r}), hospitalMass p t₀ t S) :
    hospitalFrequency p t₀ t (fun S => S.erase c = {d}) c =
      hospitalFrequency p t₀ t (fun S => S.erase c = {r}) c

end WantedExt.Biology.StatisticalGenetics.BerksonBiasWanted
