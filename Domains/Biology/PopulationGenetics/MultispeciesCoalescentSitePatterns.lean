/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Phylogenetics.JukesCantor
public import Domains.Biology.PopulationGenetics.MultispeciesCoalescent
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Site patterns of three species under the multispecies coalescent

Three species `A`, `B`, `C`, one sequence sampled from each, evolve under the multispecies
coalescent with a molecular clock and the Jukes–Cantor substitution model. A rooted species
tree on three species is one of `((A, B), C)`, `((B, C), A)` and `((C, A), B)`
(`RootedTriple`, named by its cherry); it has two divergence times `τ₀ > τ₁ > 0` and the
population size parameters `θ₀` of the root population and `θ₁` of the ancestor of the
cherry, all measured in expected numbers of mutations per site (`Params`).

At a site the three sequences show one of five patterns (`SitePattern`): `xxx`, `xxy`
(`A` and `B` agree, `C` differs), `yxx` (`B` and `C` agree), `xyx` (`A` and `C` agree) and
`xyz`. Given a gene tree with node ages `t₀ > t₁`, the Jukes–Cantor model gives the pattern
probabilities `patternProb`, with the closed forms of Zhu and Yang's equation (3)
(`patternProb_eq`). Averaging them over the multispecies-coalescent density of the gene tree
and its node ages (`mscDensity`, their equation (2)) gives the marginal site-pattern
probabilities `marginalPatternProb`. The *independent-sites maximum likelihood* method
(isml) treats every site as an independent draw from these marginal probabilities and
maximizes `ismlLikelihood` over the species tree and its parameters.

## Main results

* `patternProb_eq`: the Jukes–Cantor site-pattern probabilities on a gene tree, in closed form.
* `integral_mscDensity`, `integral_mscDensity_eq_geneTreeProb`: the density gives the gene trees
  Hudson's probabilities `1 - (2/3) e^{-t}` and `(1/3) e^{-t}`, those of `geneTreeProb`, with
  internal branch `t = 2 (τ₀ - τ₁) / θ₁` in coalescent units.
* `sum_marginalPatternProb`, `marginalPatternProb_pos`: the marginal site-pattern probabilities
  form a probability distribution.
* `marginalPatternProb_lt`, `marginalPatternProb_eq_of_ne`: under the true species tree, the
  pattern in which the two cherry species agree is strictly more probable than each of the
  two other such patterns, which are equally probable.
* `ismlLikelihood_lt`: if the pooled count of the cherry pattern of a tree exceeds those of
  the two other such patterns, that tree has a strictly larger likelihood than each other
  tree at every parameter value; `IsIsmlEstimate.eq`: every isml estimate is that tree.
* `isml_selects_majority_site_pattern`: both together (Zhu and Yang 2021, Theorem 3).

## References

* R. R. Hudson, "Testing the constant-rate neutral allele model with protein sequence data",
  Evolution 37 (1983) 203–217.
* T. Zhu and Z. Yang, "Complexity of the simplest species tree problem", Mol. Biol. Evol. 38
  (2021) 3993–4009, Theorem 3, equations (2), (3), (13) and (14).
* Z. Yang, "Statistical properties of the maximum likelihood method of phylogenetic
  estimation and comparison with distance matrix methods", Syst. Biol. 43 (1994) 329–342.
-/

@[expose] public section

open Real MeasureTheory Set Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent.SitePatterns

open MathlibExt.Biology.Phylogenetics.JukesCantor

/-! ### Trees and site patterns -/

/-- The three rooted binary trees on three species (or sequences) `A`, `B`, `C`, named by
their cherry: `ab` is `((A, B), C)`, `bc` is `((B, C), A)` and `ca` is `((C, A), B)`. Zhu and
Yang call them `S₁`, `S₂`, `S₃` as species trees and `G₁`, `G₂`, `G₃` as gene trees. -/
inductive RootedTriple
  /-- The tree `((A, B), C)`. -/
  | ab
  /-- The tree `((B, C), A)`. -/
  | bc
  /-- The tree `((C, A), B)`. -/
  | ca
  deriving DecidableEq

instance : Fintype RootedTriple :=
  ⟨{.ab, .bc, .ca}, fun G => by cases G <;> decide⟩

theorem RootedTriple.univ_eq : (Finset.univ : Finset RootedTriple) = {.ab, .bc, .ca} := rfl

/-- The five site patterns of three aligned nucleotides at the sequences `A`, `B`, `C`, for
distinct nucleotides `x`, `y`, `z`, read in the order `A`, `B`, `C`. -/
inductive SitePattern
  /-- All three nucleotides agree. -/
  | xxx
  /-- `A` and `B` agree and `C` differs. -/
  | xxy
  /-- `B` and `C` agree and `A` differs. -/
  | yxx
  /-- `A` and `C` agree and `B` differs. -/
  | xyx
  /-- All three nucleotides differ. -/
  | xyz
  deriving DecidableEq

instance : Fintype SitePattern :=
  ⟨{.xxx, .xxy, .yxx, .xyx, .xyz}, fun j => by cases j <;> decide⟩

theorem SitePattern.univ_eq :
    (Finset.univ : Finset SitePattern) = {.xxx, .xxy, .yxx, .xyx, .xyz} := rfl

/-- The site pattern in which the two species of the cherry of a tree agree and the third
differs: `xxy` for `((A, B), C)`, `yxx` for `((B, C), A)` and `xyx` for `((C, A), B)`. -/
def RootedTriple.cherryPattern : RootedTriple → SitePattern
  | .ab => .xxy
  | .bc => .yxx
  | .ca => .xyx

/-- The site pattern of the nucleotides `a`, `b`, `c` at the sequences `A`, `B`, `C`. -/
def sitePattern (a b c : Fin 4) : SitePattern :=
  if a = b then (if b = c then .xxx else .xxy)
  else if b = c then .yxx
  else if a = c then .xyx
  else .xyz

/-! ### Site-pattern probabilities on a gene tree -/

/-- The Jukes–Cantor probability of the nucleotides `x`, `y` at the two sequences of the
cherry and `z` at the third sequence of a clock gene tree whose root has age `t₀` and whose
cherry has age `t₁`, ages measured in expected substitutions per site (rate `μ = 1`): the
root nucleotide `r` is drawn from the stationary distribution, uniform on the four
nucleotides, and evolves along the branches of lengths `t₀` (to the third sequence),
`t₀ - t₁` (to the cherry's ancestor, with nucleotide `s`) and `t₁` (to each cherry
sequence). -/
def cherrySiteProb (t₀ t₁ : ℝ) (x y z : Fin 4) : ℝ :=
  ∑ r, ∑ s, 1 / 4 * jcProb 1 t₀ r z * jcProb 1 (t₀ - t₁) r s * jcProb 1 t₁ s x *
    jcProb 1 t₁ s y

/-- The Jukes–Cantor probability of the nucleotides `a`, `b`, `c` at the sequences `A`, `B`,
`C`, on the gene tree `G` with root age `t₀` and cherry age `t₁`. -/
def siteProb : RootedTriple → ℝ → ℝ → Fin 4 → Fin 4 → Fin 4 → ℝ
  | .ab, t₀, t₁, a, b, c => cherrySiteProb t₀ t₁ a b c
  | .bc, t₀, t₁, a, b, c => cherrySiteProb t₀ t₁ b c a
  | .ca, t₀, t₁, a, b, c => cherrySiteProb t₀ t₁ c a b

/-- The probability of the site pattern `j` on the gene tree `G` with root age `t₀` and cherry
age `t₁` under the Jukes–Cantor model: the sum of `siteProb` over the nucleotides that show
the pattern. -/
def patternProb (G : RootedTriple) (t₀ t₁ : ℝ) (j : SitePattern) : ℝ :=
  ∑ a, ∑ b, ∑ c, if sitePattern a b c = j then siteProb G t₀ t₁ a b c else 0

/-! ### The multispecies coalescent with three species -/

/-- The parameters of a three-species tree under the multispecies coalescent: the divergence
times `τ₀` of the root and `τ₁ < τ₀` of the cherry, and the population size parameters `θ₀` of
the root population and `θ₁` of the population ancestral to the cherry, all positive and
measured in expected numbers of mutations per site (`θ = 4 N μ`). -/
structure Params where
  /-- The divergence time of the root. -/
  τ₀ : ℝ
  /-- The divergence time of the cherry. -/
  τ₁ : ℝ
  /-- The population size parameter of the root population. -/
  θ₀ : ℝ
  /-- The population size parameter of the population ancestral to the cherry. -/
  θ₁ : ℝ
  τ₁_pos : 0 < τ₁
  τ₁_lt_τ₀ : τ₁ < τ₀
  θ₀_pos : 0 < θ₀
  θ₁_pos : 0 < θ₁

/-- The node ages `t = (t₀, t₁)` at which the two cherry sequences coalesce in the population
ancestral to the cherry: `τ₁ < t₁ < τ₀ < t₀`. -/
def cherryRegion (p : Params) : Set (ℝ × ℝ) := Ioi p.τ₀ ×ˢ Ioo p.τ₁ p.τ₀

/-- The node ages `t = (t₀, t₁)` at which all three sequences reach the root population before
coalescing: `τ₀ < t₁ < t₀`. -/
def rootRegion (p : Params) : Set (ℝ × ℝ) := {t | p.τ₀ < t.2 ∧ t.2 < t.1}

/-- The density of the node ages `t = (t₀, t₁)` of the gene tree that matches the species
tree, when its cherry sequences coalesce in the population ancestral to the cherry (on
`cherryRegion`): rate `2 / θ₁` from `τ₁`, then rate `2 / θ₀` from `τ₀`. -/
def cherryDensity (p : Params) (t : ℝ × ℝ) : ℝ :=
  2 / p.θ₁ * exp (-2 * (t.2 - p.τ₁) / p.θ₁) * (2 / p.θ₀ * exp (-2 * (t.1 - p.τ₀) / p.θ₀))

/-- The density of the node ages `t = (t₀, t₁)` of each of the three gene trees when no
coalescence happens before the root population (on `rootRegion`): the probability
`exp (-2 (τ₀ - τ₁) / θ₁)` that the cherry sequences do not coalesce before `τ₀`, then the first
coalescence, of a given pair among three lineages, at rate `2 / θ₀` with total rate `6 / θ₀`,
then the second at rate `2 / θ₀`. -/
def rootDensity (p : Params) (t : ℝ × ℝ) : ℝ :=
  exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁) *
    (2 / p.θ₀ * (2 / p.θ₀) * exp (-6 * (t.2 - p.τ₀) / p.θ₀ - 2 * (t.1 - t.2) / p.θ₀))

/-- **The multispecies-coalescent density** of the gene tree `G` and its node ages
`t = (t₀, t₁)` (root, cherry) on the species tree `S` with parameters `p` (Zhu and Yang 2021,
equation (2)): the gene tree that matches the species tree gets `cherryDensity` on
`cherryRegion`, and each of the three gene trees gets `rootDensity` on `rootRegion`. -/
def mscDensity (S : RootedTriple) (p : Params) (G : RootedTriple) (t : ℝ × ℝ) : ℝ :=
  (if G = S then (cherryRegion p).indicator (cherryDensity p) t else 0) +
    (rootRegion p).indicator (rootDensity p) t

/-- **The marginal site-pattern probabilities** `p̄ⱼ(S, p)` (Zhu and Yang 2021, equation (13)):
the Jukes–Cantor probability `patternProb` of the site pattern `j`, averaged over the
multispecies-coalescent density `mscDensity` of the gene tree and its node ages on the species
tree `S` with parameters `p`. -/
def marginalPatternProb (S : RootedTriple) (p : Params) (j : SitePattern) : ℝ :=
  ∫ t, ∑ G, mscDensity S p G t * patternProb G t.1 t.2 j

/-- **The independent-sites likelihood** of the species tree `S` with parameters `p` for the
site-pattern counts `x` pooled across loci (Zhu and Yang 2021, equation (14)): every site is an
independent draw from the marginal site-pattern probabilities. -/
def ismlLikelihood (x : SitePattern → ℕ) (S : RootedTriple) (p : Params) : ℝ :=
  ∏ j, marginalPatternProb S p j ^ x j

/-- The species tree `S` with parameters `p` is an *isml estimate* for the pooled site-pattern
counts `x`: it maximizes the independent-sites likelihood over the three species trees and
all their parameters. -/
def IsIsmlEstimate (x : SitePattern → ℕ) (S : RootedTriple) (p : Params) : Prop :=
  ∀ S' p', ismlLikelihood x S' p' ≤ ismlLikelihood x S p

/-! ### Closed forms of the pattern probabilities -/

/-- `xxx` on a gene tree with root age `t₀` and cherry age `t₁`. -/
private def probSame (t₀ t₁ : ℝ) : ℝ :=
  (1 + 3 * exp (-4 * t₁ / 3) ^ 2 + 6 * exp (-8 * t₀ / 3) +
    6 * exp (-8 * t₀ / 3) * exp (-4 * t₁ / 3)) / 16

/-- The pattern in which the cherry sequences agree. -/
private def probCherry (t₀ t₁ : ℝ) : ℝ :=
  (3 + 9 * exp (-4 * t₁ / 3) ^ 2 - 6 * exp (-8 * t₀ / 3) -
    6 * exp (-8 * t₀ / 3) * exp (-4 * t₁ / 3)) / 16

/-- Each of the two patterns in which a cherry sequence agrees with the third sequence. -/
private def probOther (t₀ t₁ : ℝ) : ℝ :=
  (3 - 3 * exp (-4 * t₁ / 3) ^ 2 + 6 * exp (-8 * t₀ / 3) -
    6 * exp (-8 * t₀ / 3) * exp (-4 * t₁ / 3)) / 16

/-- `xyz`. -/
private def probDistinct (t₀ t₁ : ℝ) : ℝ :=
  (6 - 6 * exp (-4 * t₁ / 3) ^ 2 - 12 * exp (-8 * t₀ / 3) +
    12 * exp (-8 * t₀ / 3) * exp (-4 * t₁ / 3)) / 16

private theorem cherrySiteProb_eq (t₀ t₁ : ℝ) (x y z : Fin 4) :
    cherrySiteProb t₀ t₁ x y z =
      if x = y then (if y = z then probSame t₀ t₁ / 4 else probCherry t₀ t₁ / 12)
      else if y = z ∨ x = z then probOther t₀ t₁ / 12 else probDistinct t₀ t₁ / 24 := by
  have h8 : exp (-8 * t₀ / 3) =
      exp (-4 * 1 * (t₀ - t₁) / 3) ^ 2 * exp (-4 * 1 * t₁ / 3) ^ 2 := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]; ring_nf
  have h0 : exp (-4 * 1 * t₀ / 3) = exp (-4 * 1 * (t₀ - t₁) / 3) * exp (-4 * 1 * t₁ / 3) := by
    rw [← exp_add]; ring_nf
  have h1 : exp (-4 * t₁ / 3) = exp (-4 * 1 * t₁ / 3) := by ring_nf
  simp only [cherrySiteProb, probSame, probCherry, probOther, probDistinct, jcProb, h8, h0, h1]
  generalize exp (-4 * 1 * (t₀ - t₁) / 3) = a
  generalize exp (-4 * 1 * t₁ / 3) = b
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [Fin.sum_univ_four] <;> ring

private theorem patternProb_eq_aux (G : RootedTriple) (t₀ t₁ : ℝ) (j : SitePattern) :
    patternProb G t₀ t₁ j =
      if j = .xxx then probSame t₀ t₁ else if j = .xyz then probDistinct t₀ t₁
      else if j = G.cherryPattern then probCherry t₀ t₁ else probOther t₀ t₁ := by
  cases G <;> cases j <;>
    simp [patternProb, siteProb, cherrySiteProb_eq, sitePattern, RootedTriple.cherryPattern,
      Fin.sum_univ_four] <;> ring

/-- **The Jukes–Cantor site-pattern probabilities on a gene tree** (Zhu and Yang 2021,
equation (3); Yang 1994): with `u = exp (-8 t₀ / 3)` and `v = exp (-4 t₁ / 3)`, the
patterns `xxx`, `xyz`, the cherry pattern of `G`, and each of the two other patterns in which
two sequences agree have the probabilities `(1 + 3 v² + 6 u + 6 u v) / 16`,
`(6 - 6 v² - 12 u + 12 u v) / 16`, `(3 + 9 v² - 6 u - 6 u v) / 16` and
`(3 - 3 v² + 6 u - 6 u v) / 16`. -/
theorem patternProb_eq (G : RootedTriple) (t₀ t₁ : ℝ) (j : SitePattern) :
    patternProb G t₀ t₁ j =
      if j = .xxx then
        (1 + 3 * exp (-4 * t₁ / 3) ^ 2 + 6 * exp (-8 * t₀ / 3) +
          6 * exp (-8 * t₀ / 3) * exp (-4 * t₁ / 3)) / 16
      else if j = .xyz then
        (6 - 6 * exp (-4 * t₁ / 3) ^ 2 - 12 * exp (-8 * t₀ / 3) +
          12 * exp (-8 * t₀ / 3) * exp (-4 * t₁ / 3)) / 16
      else if j = G.cherryPattern then
        (3 + 9 * exp (-4 * t₁ / 3) ^ 2 - 6 * exp (-8 * t₀ / 3) -
          6 * exp (-8 * t₀ / 3) * exp (-4 * t₁ / 3)) / 16
      else
        (3 - 3 * exp (-4 * t₁ / 3) ^ 2 + 6 * exp (-8 * t₀ / 3) -
          6 * exp (-8 * t₀ / 3) * exp (-4 * t₁ / 3)) / 16 :=
  patternProb_eq_aux G t₀ t₁ j

theorem RootedTriple.cherryPattern_inj {S S' : RootedTriple} :
    S.cherryPattern = S'.cherryPattern ↔ S = S' := by
  cases S <;> cases S' <;> simp [RootedTriple.cherryPattern]

theorem RootedTriple.cherryPattern_ne_xxx (S : RootedTriple) : S.cherryPattern ≠ .xxx := by
  cases S <;> simp [RootedTriple.cherryPattern]

theorem RootedTriple.cherryPattern_ne_xyz (S : RootedTriple) : S.cherryPattern ≠ .xyz := by
  cases S <;> simp [RootedTriple.cherryPattern]

private theorem patternProb_cherryPattern (G S : RootedTriple) (t₀ t₁ : ℝ) :
    patternProb G t₀ t₁ S.cherryPattern =
      if S = G then probCherry t₀ t₁ else probOther t₀ t₁ := by
  simp [patternProb_eq_aux, S.cherryPattern_ne_xxx, S.cherryPattern_ne_xyz,
    RootedTriple.cherryPattern_inj]

private theorem sum_tree_patternProb (t₀ t₁ : ℝ) (j : SitePattern) :
    ∑ G, patternProb G t₀ t₁ j =
      if j = .xxx then 3 * probSame t₀ t₁ else if j = .xyz then 3 * probDistinct t₀ t₁
      else probCherry t₀ t₁ + 2 * probOther t₀ t₁ := by
  rw [RootedTriple.univ_eq]
  cases j <;> simp [patternProb_eq_aux, RootedTriple.cherryPattern] <;> ring

/-- The site-pattern probabilities on a gene tree sum to one, for all node ages. -/
theorem sum_patternProb_eq_one (G : RootedTriple) (t₀ t₁ : ℝ) :
    ∑ j, patternProb G t₀ t₁ j = 1 := by
  rw [SitePattern.univ_eq]
  cases G <;> simp [patternProb_eq_aux, RootedTriple.cherryPattern, probSame, probCherry,
    probOther, probDistinct] <;> ring

/-! ### Bounds on the pattern probabilities -/

private theorem exp_bounds {t₀ t₁ : ℝ} (h₁ : 0 < t₁) (h : t₁ < t₀) :
    0 < exp (-8 * t₀ / 3) ∧ exp (-8 * t₀ / 3) < exp (-4 * t₁ / 3) ^ 2 ∧
      0 < exp (-4 * t₁ / 3) ∧ exp (-4 * t₁ / 3) < 1 := by
  refine ⟨exp_pos _, ?_, exp_pos _, ?_⟩
  · rw [← exp_nat_mul]; exact exp_lt_exp.2 (by push_cast; linarith)
  · rw [← exp_zero]; exact exp_lt_exp.2 (by linarith)

private theorem patternProb_pos (G : RootedTriple) {t₀ t₁ : ℝ} (h₁ : 0 < t₁) (h : t₁ < t₀)
    (j : SitePattern) : 0 < patternProb G t₀ t₁ j := by
  obtain ⟨hu, huv, hv, hv1⟩ := exp_bounds h₁ h
  rw [patternProb_eq_aux]
  simp only [probSame, probCherry, probOther, probDistinct]
  generalize exp (-8 * t₀ / 3) = u at *
  generalize exp (-4 * t₁ / 3) = v at *
  have hvv : v ^ 2 < v := by nlinarith
  have hw : 0 < 1 + v - 2 * u := by linarith
  split_ifs <;> nlinarith [mul_pos hu hv, mul_pos hv hv, mul_pos (sub_pos.2 hv1) hu,
    mul_pos (sub_pos.2 hv1) hw]

private theorem patternProb_le_one (G : RootedTriple) {t₀ t₁ : ℝ} (h₁ : 0 < t₁) (h : t₁ < t₀)
    (j : SitePattern) : patternProb G t₀ t₁ j ≤ 1 := by
  obtain ⟨hu, huv, hv, hv1⟩ := exp_bounds h₁ h
  rw [patternProb_eq_aux]
  simp only [probSame, probCherry, probOther, probDistinct]
  generalize exp (-8 * t₀ / 3) = u at *
  generalize exp (-4 * t₁ / 3) = v at *
  have hvv : v ^ 2 < v := by nlinarith
  have hw : 0 < 1 + v - 2 * u := by linarith
  split_ifs <;> nlinarith [mul_pos hu hv, mul_pos hv hv, mul_pos (sub_pos.2 hv1) hu,
    mul_pos (sub_pos.2 hv1) hw, mul_pos hv hw]

private theorem probOther_lt_probCherry {t₀ t₁ : ℝ} (h₁ : 0 < t₁) (h : t₁ < t₀) :
    probOther t₀ t₁ < probCherry t₀ t₁ := by
  obtain ⟨-, huv, -, -⟩ := exp_bounds h₁ h
  simp only [probCherry, probOther]
  linarith

private theorem continuous_patternProb (G : RootedTriple) (j : SitePattern) :
    Continuous fun t : ℝ × ℝ => patternProb G t.1 t.2 j := by
  simp_rw [patternProb_eq_aux]
  refine continuous_if_const _ (fun _ => ?_) fun _ => continuous_if_const _ (fun _ => ?_)
    fun _ => continuous_if_const _ (fun _ => ?_) fun _ => ?_ <;>
    · simp only [probSame, probCherry, probOther, probDistinct]; fun_prop

/-! ### The density -/

private theorem pos_of_mem {p : Params} {t : ℝ × ℝ} (ht : t ∈ cherryRegion p ∪ rootRegion p) :
    0 < t.2 ∧ t.2 < t.1 := by
  have := p.τ₁_pos
  have := p.τ₁_lt_τ₀
  rcases ht with ⟨h0, h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith, by simp only [Set.mem_Ioi] at h0; linarith⟩
  · exact ⟨by linarith, h2⟩

private theorem measurableSet_rootRegion (p : Params) : MeasurableSet (rootRegion p) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_fst)

private theorem cherryDensity_pos (p : Params) (t : ℝ × ℝ) : 0 < cherryDensity p t := by
  have := p.θ₀_pos
  have := p.θ₁_pos
  unfold cherryDensity
  positivity

private theorem rootDensity_pos (p : Params) (t : ℝ × ℝ) : 0 < rootDensity p t := by
  have := p.θ₀_pos
  unfold rootDensity
  positivity

private theorem mscDensity_nonneg (S : RootedTriple) (p : Params) (G : RootedTriple)
    (t : ℝ × ℝ) : 0 ≤ mscDensity S p G t := by
  unfold mscDensity
  refine add_nonneg ?_ (indicator_nonneg (fun t _ => (rootDensity_pos p t).le) t)
  split_ifs
  · exact indicator_nonneg (fun t _ => (cherryDensity_pos p t).le) t
  · exact le_rfl

private theorem mscDensity_eq_zero {S : RootedTriple} {p : Params} {G : RootedTriple}
    {t : ℝ × ℝ} (ht : t ∉ cherryRegion p ∪ rootRegion p) : mscDensity S p G t = 0 := by
  simp only [mem_union, not_or] at ht
  simp [mscDensity, indicator_of_notMem ht.1, indicator_of_notMem ht.2]

private theorem integrableOn_exp_Ioi {a k θ : ℝ} (hk : 0 < k) (hθ : 0 < θ) (b : ℝ) :
    IntegrableOn (fun x => exp (-k * (x - a) / θ)) (Ioi b) := by
  refine IntegrableOn.congr_fun ((exp_neg_integrableOn_Ioi b (div_pos hk hθ)).const_mul
    (exp (k * a / θ)) : IntegrableOn _ _ _) (fun x _ => ?_) measurableSet_Ioi
  rw [← exp_add]
  congr 1
  field_simp
  ring

private theorem integrable_cherry (p : Params) :
    Integrable ((cherryRegion p).indicator (cherryDensity p)) := by
  rw [integrable_indicator_iff
    (show MeasurableSet (cherryRegion p) from measurableSet_Ioi.prod measurableSet_Ioo)]
  have h₀ : IntegrableOn (fun x : ℝ => 2 / p.θ₀ * exp (-2 * (x - p.τ₀) / p.θ₀)) (Ioi p.τ₀) :=
    (integrableOn_exp_Ioi two_pos p.θ₀_pos p.τ₀).const_mul _
  have h₁ : IntegrableOn (fun x : ℝ => 2 / p.θ₁ * exp (-2 * (x - p.τ₁) / p.θ₁))
      (Ioo p.τ₁ p.τ₀) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  have := h₀.mul_prod h₁
  rw [IntegrableOn, cherryRegion, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [cherryDensity]
  ring

private theorem integrable_root (p : Params) :
    Integrable ((rootRegion p).indicator (rootDensity p)) := by
  rw [integrable_indicator_iff (measurableSet_rootRegion p)]
  have h₀ : IntegrableOn (fun x : ℝ => exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁) * (2 / p.θ₀ * (2 / p.θ₀)) *
      exp (-2 * (x - p.τ₀) / p.θ₀)) (Ioi p.τ₀) :=
    (integrableOn_exp_Ioi two_pos p.θ₀_pos p.τ₀).const_mul _
  have h₁ : IntegrableOn (fun x : ℝ => exp (-4 * (x - p.τ₀) / p.θ₀)) (Ioi p.τ₀) :=
    integrableOn_exp_Ioi four_pos p.θ₀_pos p.τ₀
  have := h₀.mul_prod h₁
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at this
  refine (IntegrableOn.mono_set (t := Ioi p.τ₀ ×ˢ Ioi p.τ₀) this ?_).congr_fun (fun t _ => ?_)
    (measurableSet_rootRegion p)
  · rintro t ⟨h₁, h₂⟩
    exact ⟨h₁.trans h₂, h₁⟩
  · have : exp (-6 * (t.2 - p.τ₀) / p.θ₀ - 2 * (t.1 - t.2) / p.θ₀) =
        exp (-2 * (t.1 - p.τ₀) / p.θ₀) * exp (-4 * (t.2 - p.τ₀) / p.θ₀) := by
      rw [← exp_add]
      ring_nf
    simp only [rootDensity, this]
    ring

private theorem integrable_mscDensity (S : RootedTriple) (p : Params) (G : RootedTriple) :
    Integrable (mscDensity S p G) := by
  change Integrable fun t => mscDensity S p G t
  by_cases h : G = S
  · simp only [mscDensity, h, ite_true]
    exact (integrable_cherry p).add (integrable_root p)
  · simp only [mscDensity, h, ite_false, zero_add]
    exact integrable_root p

private theorem abs_mscDensity_mul_le (S : RootedTriple) (p : Params) (G : RootedTriple)
    (j : SitePattern) (t : ℝ × ℝ) :
    |mscDensity S p G t * patternProb G t.1 t.2 j| ≤ mscDensity S p G t := by
  by_cases ht : t ∈ cherryRegion p ∪ rootRegion p
  · obtain ⟨h₁, h⟩ := pos_of_mem ht
    rw [abs_mul, abs_of_nonneg (mscDensity_nonneg S p G t),
      abs_of_nonneg (patternProb_pos G h₁ h j).le]
    exact mul_le_of_le_one_right (mscDensity_nonneg S p G t) (patternProb_le_one G h₁ h j)
  · simp [mscDensity_eq_zero ht]

private theorem mscDensity_mul_nonneg (S : RootedTriple) (p : Params) (G : RootedTriple)
    (j : SitePattern) (t : ℝ × ℝ) : 0 ≤ mscDensity S p G t * patternProb G t.1 t.2 j := by
  by_cases ht : t ∈ cherryRegion p ∪ rootRegion p
  · obtain ⟨h₁, h⟩ := pos_of_mem ht
    exact mul_nonneg (mscDensity_nonneg S p G t) (patternProb_pos G h₁ h j).le
  · simp [mscDensity_eq_zero ht]

private theorem integrable_integrand (S : RootedTriple) (p : Params) (j : SitePattern) :
    Integrable fun t => ∑ G, mscDensity S p G t * patternProb G t.1 t.2 j :=
  integrable_finsetSum _ fun G _ =>
    (integrable_mscDensity S p G).mono'
      ((integrable_mscDensity S p G).aestronglyMeasurable.mul
        (continuous_patternProb G j).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]; exact abs_mscDensity_mul_le S p G j t)

private theorem integrand_eq (S : RootedTriple) (p : Params) (j : SitePattern) (t : ℝ × ℝ) :
    ∑ G, mscDensity S p G t * patternProb G t.1 t.2 j =
      (cherryRegion p).indicator (cherryDensity p) t * patternProb S t.1 t.2 j +
        (rootRegion p).indicator (rootDensity p) t * ∑ G, patternProb G t.1 t.2 j := by
  simp only [mscDensity, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]

private theorem volume_cherryRegion_pos (p : Params) : 0 < volume (cherryRegion p) := by
  rw [cherryRegion, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioi,
    Real.volume_Ioo]
  exact ENNReal.mul_pos ENNReal.top_ne_zero
    (ENNReal.ofReal_pos.2 (sub_pos.2 p.τ₁_lt_τ₀)).ne'

/-- Two marginal site-pattern probabilities agree when the patterns play the same role in
their species trees. -/
private theorem marginalPatternProb_congr {S S' : RootedTriple} {j j' : SitePattern}
    (p : Params) (h₀ : j = .xxx ↔ j' = .xxx) (h₄ : j = .xyz ↔ j' = .xyz)
    (hc : j = S.cherryPattern ↔ j' = S'.cherryPattern) :
    marginalPatternProb S p j = marginalPatternProb S' p j' := by
  unfold marginalPatternProb
  congr 1
  funext t
  rw [integrand_eq, integrand_eq, sum_tree_patternProb, sum_tree_patternProb, patternProb_eq_aux,
    patternProb_eq_aux]
  simp only [h₀, h₄, hc]

/-! ### Gene-tree probabilities -/

/-- The cherry of a rooted triple, as a set of the species `A = 0`, `B = 1`, `C = 2`. -/
def RootedTriple.cherry : RootedTriple → Finset (Fin 3)
  | .ab => {0, 1}
  | .bc => {1, 2}
  | .ca => {0, 2}

private theorem integral_exp_Ioi {a k θ : ℝ} (hk : 0 < k) (hθ : 0 < θ) (b : ℝ) :
    ∫ x in Ioi b, exp (-k * (x - a) / θ) = θ / k * exp (-k * (b - a) / θ) := by
  have h : ∀ x, exp (-k * (x - a) / θ) = exp (k * a / θ) * exp (-(k / θ) * x) := fun x => by
    rw [← exp_add]; congr 1; field_simp; ring
  simp_rw [h]
  rw [integral_const_mul, integral_exp_mul_Ioi (by have := div_pos hk hθ; linarith)]
  field_simp

private theorem integral_cherry (p : Params) :
    ∫ t, (cherryRegion p).indicator (cherryDensity p) t = 1 - exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁) := by
  have hθ₀ := p.θ₀_pos
  have hθ₁ := p.θ₁_pos
  rw [integral_indicator
      (show MeasurableSet (cherryRegion p) from measurableSet_Ioi.prod measurableSet_Ioo),
    cherryRegion, Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun x : ℝ => 2 / p.θ₀ * exp (-2 * (x - p.τ₀) / p.θ₀))
    (fun x : ℝ => 2 / p.θ₁ * exp (-2 * (x - p.τ₁) / p.θ₁)) (Ioi p.τ₀) (Ioo p.τ₁ p.τ₀)
  rw [show cherryDensity p = fun t : ℝ × ℝ => 2 / p.θ₀ * exp (-2 * (t.1 - p.τ₀) / p.θ₀) *
      (2 / p.θ₁ * exp (-2 * (t.2 - p.τ₁) / p.θ₁)) from funext fun t => by
        simp only [cherryDensity]; ring, h]
  have hIoc : ∫ x in Ioo p.τ₁ p.τ₀, exp (-2 * (x - p.τ₁) / p.θ₁) =
      (∫ x in Ioi p.τ₁, exp (-2 * (x - p.τ₁) / p.θ₁)) -
        ∫ x in Ioi p.τ₀, exp (-2 * (x - p.τ₁) / p.θ₁) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← Ioc_union_Ioi_eq_Ioi p.τ₁_lt_τ₀.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((integrableOn_exp_Ioi (a := p.τ₁) two_pos hθ₁ p.τ₁).mono_set Ioc_subset_Ioi_self)
        (integrableOn_exp_Ioi (a := p.τ₁) two_pos hθ₁ p.τ₀)]
    ring
  rw [integral_const_mul, integral_const_mul, hIoc, integral_exp_Ioi (a := p.τ₀) two_pos hθ₀,
    integral_exp_Ioi (a := p.τ₁) two_pos hθ₁ p.τ₁, integral_exp_Ioi (a := p.τ₁) two_pos hθ₁ p.τ₀]
  simp only [sub_self, mul_zero, zero_div, exp_zero]
  field_simp

private theorem integral_root (p : Params) :
    ∫ t, (rootRegion p).indicator (rootDensity p) t =
      exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁) / 3 := by
  have hθ₀ := p.θ₀_pos
  rw [Measure.volume_eq_prod, integral_prod_symm _ (by
    rw [← Measure.volume_eq_prod]; exact integrable_root p)]
  have hin : ∀ y : ℝ, ∫ x, (rootRegion p).indicator (rootDensity p) (x, y) =
      (Ioi p.τ₀).indicator (fun y => exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁) * (2 / p.θ₀) *
        exp (-6 * (y - p.τ₀) / p.θ₀)) y := by
    intro y
    by_cases hy : p.τ₀ < y
    · have : (fun x => (rootRegion p).indicator (rootDensity p) (x, y)) =
          (Ioi y).indicator fun x => exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁) * (2 / p.θ₀ * (2 / p.θ₀)) *
            exp (-6 * (y - p.τ₀) / p.θ₀) * exp (-2 * (x - y) / p.θ₀) := by
        funext x
        by_cases hx : y < x
        · rw [indicator_of_mem (show (x, y) ∈ rootRegion p from ⟨hy, hx⟩),
            indicator_of_mem (show x ∈ Ioi y from hx), rootDensity, sub_eq_add_neg _ (2 * _ / _),
            exp_add]
          simp only
          ring_nf
        · rw [indicator_of_notMem (fun h : (x, y) ∈ rootRegion p => hx h.2), indicator_of_notMem hx]
      rw [this, integral_indicator measurableSet_Ioi, integral_const_mul,
        integral_exp_Ioi two_pos hθ₀, indicator_of_mem (show y ∈ Ioi p.τ₀ from hy)]
      simp only [sub_self, mul_zero, zero_div, exp_zero]
      field_simp
    · have : (fun x => (rootRegion p).indicator (rootDensity p) (x, y)) = fun _ => 0 := by
        funext x
        exact indicator_of_notMem (fun h : (x, y) ∈ rootRegion p => hy h.1) _
      rw [this, integral_zero, indicator_of_notMem hy]
  simp_rw [hin]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_Ioi (by norm_num : (0 : ℝ) < 6) hθ₀]
  simp only [sub_self, mul_zero, zero_div, exp_zero]
  field_simp
  ring

/-- **The gene-tree probabilities of the density** (Hudson 1983; Zhu and Yang 2021, equation
(1)): integrating `mscDensity` over the node ages gives the gene tree that matches the species
tree the probability `1 - (2/3) φ` and each other gene tree the probability `φ / 3`, where
`φ = exp (-2 (τ₀ - τ₁) / θ₁)` is the probability that the cherry sequences do not coalesce
before `τ₀`. -/
theorem integral_mscDensity (S : RootedTriple) (p : Params) (G : RootedTriple) :
    ∫ t, mscDensity S p G t =
      if G = S then 1 - 2 / 3 * exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁)
      else exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁) / 3 := by
  by_cases h : G = S
  · simp only [mscDensity, h, ite_true]
    rw [integral_add (integrable_cherry p) (integrable_root p), integral_cherry, integral_root]
    ring
  · simp only [mscDensity, h, ite_false, zero_add]
    exact integral_root p

/-- **The density agrees with the multispecies coalescent**: on the species tree
`((A, B), C)`, the probability that `mscDensity` gives the gene tree `G` is the probability
`geneTreeProb` of the multispecies coalescent on the species tree `triple` whose internal
branch has the length `2 (τ₀ - τ₁) / θ₁` in coalescent units. -/
theorem integral_mscDensity_eq_geneTreeProb (p : Params) (G : RootedTriple) :
    ∫ t, mscDensity .ab p G t =
      geneTreeProb (triple (2 * (p.τ₀ - p.τ₁) / p.θ₁)) (· = tripleTree G.cherry) := by
  have he : exp (-(2 * (p.τ₀ - p.τ₁) / p.θ₁)) = exp (-2 * (p.τ₀ - p.τ₁) / p.θ₁) := by ring_nf
  set t := 2 * (p.τ₀ - p.τ₁) / p.θ₁
  rw [integral_mscDensity]
  cases G <;> simp only [reduceCtorEq, ite_true, ite_false]
  · exact Eq.trans (by rw [he]) (geneTreeProb_triple_matching t).symm
  · exact Eq.trans (by rw [he]; ring) (geneTreeProb_triple_cherry_12 t).symm
  · exact Eq.trans (by rw [he]; ring) (geneTreeProb_triple_cherry_02 t).symm

/-- **The marginal site-pattern probabilities form a probability distribution**: they are
positive (`marginalPatternProb_pos`) and sum to one. -/
theorem sum_marginalPatternProb (S : RootedTriple) (p : Params) :
    ∑ j, marginalPatternProb S p j = 1 := by
  unfold marginalPatternProb
  rw [← integral_finsetSum _ fun j _ => integrable_integrand S p j]
  simp_rw [Finset.sum_comm (γ := SitePattern), ← Finset.mul_sum, sum_patternProb_eq_one, mul_one]
  rw [integral_finsetSum _ fun G _ => integrable_mscDensity S p G]
  simp only [integral_mscDensity, RootedTriple.univ_eq]
  cases S <;> simp <;> ring

/-! ### Zhu and Yang's Theorem 3 -/

/-- Every marginal site-pattern probability is positive. -/
theorem marginalPatternProb_pos (S : RootedTriple) (p : Params) (j : SitePattern) :
    0 < marginalPatternProb S p j := by
  unfold marginalPatternProb
  refine (integral_pos_iff_support_of_nonneg
    (fun t => Finset.sum_nonneg fun G _ => mscDensity_mul_nonneg S p G j t)
    (integrable_integrand S p j)).2 ((volume_cherryRegion_pos p).trans_le (measure_mono ?_))
  intro t ht
  obtain ⟨h₁, h⟩ := pos_of_mem (Or.inl ht : t ∈ cherryRegion p ∪ rootRegion p)
  rw [Function.mem_support, integrand_eq, indicator_of_mem ht]
  refine (add_pos_of_pos_of_nonneg (mul_pos (cherryDensity_pos p t) (patternProb_pos S h₁ h j))
    (mul_nonneg (indicator_nonneg (fun t _ => (rootDensity_pos p t).le) t)
      (Finset.sum_nonneg fun G _ => (patternProb_pos G h₁ h j).le))).ne'

/-- **The cherry pattern is the most probable** (Zhu and Yang 2021, Theorem 3(a)): under the
species tree `S`, the site pattern in which the two cherry species agree is strictly more
probable than each other pattern in which two species agree. -/
theorem marginalPatternProb_lt (S : RootedTriple) (p : Params) {S' : RootedTriple}
    (h : S' ≠ S) :
    marginalPatternProb S p S'.cherryPattern < marginalPatternProb S p S.cherryPattern := by
  rw [← sub_pos, marginalPatternProb, marginalPatternProb,
    ← integral_sub (integrable_integrand S p _) (integrable_integrand S p _)]
  have heq : ∀ t : ℝ × ℝ,
      ∑ G, mscDensity S p G t * patternProb G t.1 t.2 S.cherryPattern -
        ∑ G, mscDensity S p G t * patternProb G t.1 t.2 S'.cherryPattern =
      (cherryRegion p).indicator (cherryDensity p) t *
        (probCherry t.1 t.2 - probOther t.1 t.2) := by
    intro t
    rw [integrand_eq, integrand_eq, patternProb_cherryPattern, patternProb_cherryPattern,
      sum_tree_patternProb, sum_tree_patternProb]
    simp only [h, ite_true, ite_false, S.cherryPattern_ne_xxx, S.cherryPattern_ne_xyz,
      S'.cherryPattern_ne_xxx, S'.cherryPattern_ne_xyz]
    ring
  have hnn : ∀ t : ℝ × ℝ, 0 ≤ (cherryRegion p).indicator (cherryDensity p) t *
      (probCherry t.1 t.2 - probOther t.1 t.2) := by
    intro t
    by_cases ht : t ∈ cherryRegion p
    · obtain ⟨h₁, h₂⟩ := pos_of_mem (Or.inl ht : t ∈ cherryRegion p ∪ rootRegion p)
      exact mul_nonneg (indicator_nonneg (fun t _ => (cherryDensity_pos p t).le) t)
        (sub_pos.2 (probOther_lt_probCherry h₁ h₂)).le
    · simp [indicator_of_notMem ht]
  simp_rw [heq]
  refine (integral_pos_iff_support_of_nonneg hnn ?_).2
    ((volume_cherryRegion_pos p).trans_le (measure_mono fun t ht => ?_))
  · refine ((integrable_integrand S p S.cherryPattern).sub
      (integrable_integrand S p S'.cherryPattern)).congr (Filter.Eventually.of_forall heq)
  · obtain ⟨h₁, h₂⟩ := pos_of_mem (Or.inl ht : t ∈ cherryRegion p ∪ rootRegion p)
    rw [Function.mem_support, indicator_of_mem ht]
    exact (mul_pos (cherryDensity_pos p t) (sub_pos.2 (probOther_lt_probCherry h₁ h₂))).ne'

/-- **The two other patterns are equally probable** (Zhu and Yang 2021, Theorem 3(a)): under
the species tree `S`, the two site patterns in which a cherry species agrees with the third
species have the same probability. -/
theorem marginalPatternProb_eq_of_ne (S : RootedTriple) (p : Params) {S' S'' : RootedTriple}
    (h' : S' ≠ S) (h'' : S'' ≠ S) :
    marginalPatternProb S p S'.cherryPattern = marginalPatternProb S p S''.cherryPattern :=
  marginalPatternProb_congr p (by simp [S'.cherryPattern_ne_xxx, S''.cherryPattern_ne_xxx])
    (by simp [S'.cherryPattern_ne_xyz, S''.cherryPattern_ne_xyz])
    (by simp [RootedTriple.cherryPattern_inj, h', h''])

/-- Relabelling the species: the marginal probabilities under `S'` are those under `S` with the
cherry patterns of `S` and `S'` exchanged. -/
private theorem marginalPatternProb_swap (p : Params) (S S' : RootedTriple) (j : SitePattern) :
    marginalPatternProb S' p j =
      marginalPatternProb S p (Equiv.swap S.cherryPattern S'.cherryPattern j) := by
  refine marginalPatternProb_congr p ?_ ?_ ?_
  · rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (S.cherryPattern_ne_xxx).symm
      (S'.cherryPattern_ne_xxx).symm]
  · rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne (S.cherryPattern_ne_xyz).symm
      (S'.cherryPattern_ne_xyz).symm]
  · rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

private theorem pow_mul_pow_lt {a b : ℝ} {m n : ℕ} (hb : 0 < b) (hab : b < a) (hnm : n < m) :
    a ^ n * b ^ m < a ^ m * b ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnm
  have ha : 0 < a := hb.trans hab
  have hk : b ^ (k + 1) < a ^ (k + 1) := pow_lt_pow_left₀ hab hb.le (Nat.succ_ne_zero k)
  calc a ^ n * b ^ (n + k + 1) = a ^ n * b ^ n * b ^ (k + 1) := by ring
    _ < a ^ n * b ^ n * a ^ (k + 1) := mul_lt_mul_of_pos_left hk (by positivity)
    _ = a ^ (n + k + 1) * b ^ n := by ring

/-- **Isml prefers the tree of the majority pattern at every parameter value** (Zhu and Yang
2021, proof of Theorem 3(b)): if the pooled count of the cherry pattern of `S` exceeds the
pooled counts of the two other patterns in which two species agree, then at every parameter
value `p` each other species tree has a strictly smaller independent-sites likelihood than
`S`. -/
theorem ismlLikelihood_lt {x : SitePattern → ℕ} {S : RootedTriple}
    (hx : ∀ S', S' ≠ S → x S'.cherryPattern < x S.cherryPattern) (p : Params)
    {S' : RootedTriple} (h : S' ≠ S) : ismlLikelihood x S' p < ismlLikelihood x S p := by
  set c := S.cherryPattern
  set c' := S'.cherryPattern
  set σ := Equiv.swap c c'
  set q := marginalPatternProb S p
  have hcc : c' ≠ c := fun e => h (RootedTriple.cherryPattern_inj.1 e)
  have hL' : ismlLikelihood x S' p = ∏ j, q j ^ x (σ j) := by
    unfold ismlLikelihood
    simp_rw [marginalPatternProb_swap p S S']
    refine Eq.trans ?_ (Equiv.prod_comp σ fun j => q j ^ x (σ j))
    simp only [σ, Equiv.swap_apply_self]
    rfl
  have hσ : ∀ j ∈ (Finset.univ.erase c).erase c', x (σ j) = x j := fun j hj => by
    obtain ⟨h₁, hj⟩ := Finset.mem_erase.1 hj
    rw [Equiv.swap_apply_of_ne_of_ne (Finset.mem_erase.1 hj).1 h₁]
  have hc' : c' ∈ Finset.univ.erase c := Finset.mem_erase.2 ⟨hcc, Finset.mem_univ _⟩
  have hR : 0 < ∏ j ∈ (Finset.univ.erase c).erase c', q j ^ x j :=
    Finset.prod_pos fun j _ => pow_pos (marginalPatternProb_pos S p j) _
  rw [hL', ismlLikelihood, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ _ hc',
    ← Finset.mul_prod_erase _ _ hc', Finset.prod_congr rfl fun j hj => by rw [hσ j hj]]
  simp only [σ, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have key := pow_mul_pow_lt (marginalPatternProb_pos S p c')
    (marginalPatternProb_lt S p h) (hx S' h)
  calc q c ^ x c' * (q c' ^ x c * ∏ j ∈ (Finset.univ.erase c).erase c', q j ^ x j)
      = (q c ^ x c' * q c' ^ x c) * ∏ j ∈ (Finset.univ.erase c).erase c', q j ^ x j := by ring
    _ < (q c ^ x c * q c' ^ x c') * ∏ j ∈ (Finset.univ.erase c).erase c', q j ^ x j :=
      mul_lt_mul_of_pos_right key hR
    _ = _ := by ring

/-- **Isml infers the tree of the majority pattern** (Zhu and Yang 2021, Theorem 3(b)): if the
pooled count of the cherry pattern of `S` exceeds the pooled counts of the two other patterns
in which two species agree, every isml estimate has species tree `S`. -/
theorem IsIsmlEstimate.eq {x : SitePattern → ℕ} {S : RootedTriple}
    (hx : ∀ S', S' ≠ S → x S'.cherryPattern < x S.cherryPattern) {S' : RootedTriple}
    {p : Params} (h : IsIsmlEstimate x S' p) : S' = S := by
  by_contra hne
  exact (ismlLikelihood_lt hx p hne).not_ge (h S p)

/-- **Independent-sites likelihood selects the majority site pattern** (Zhu and Yang 2021,
Theorem 3). Three species evolve under the multispecies coalescent with a molecular clock and
the Jukes–Cantor model; `S` is one of the three rooted species trees.

1. If the true species tree is `S`, with any parameters `p`, the site pattern in which the two
   cherry species agree is strictly more probable than each of the two other patterns in which
   two species agree, and these two are equally probable: for `S = ((A, B), C)`,
   `p̄(xxy) > p̄(yxx) = p̄(xyx)`.
2. If the pooled count of the cherry pattern of `S` exceeds the pooled counts of the two other
   patterns in which two species agree (for `S = ((A, B), C)`,
   `x(xxy) > max (x(yxx), x(xyx))`), then at every parameter value each other species tree has
   a strictly smaller independent-sites likelihood than `S`, so every isml estimate, a
   maximizer of the likelihood over the three species trees and their parameters, has species
   tree `S`. -/
theorem isml_selects_majority_site_pattern (S : RootedTriple) :
    (∀ (p : Params) (S' : RootedTriple), S' ≠ S →
      marginalPatternProb S p S'.cherryPattern < marginalPatternProb S p S.cherryPattern) ∧
    (∀ (p : Params) (S' S'' : RootedTriple), S' ≠ S → S'' ≠ S →
      marginalPatternProb S p S'.cherryPattern = marginalPatternProb S p S''.cherryPattern) ∧
    ∀ x : SitePattern → ℕ, (∀ S', S' ≠ S → x S'.cherryPattern < x S.cherryPattern) →
      (∀ (p : Params) (S' : RootedTriple), S' ≠ S →
        ismlLikelihood x S' p < ismlLikelihood x S p) ∧
      ∀ (S' : RootedTriple) (p : Params), IsIsmlEstimate x S' p → S' = S :=
  ⟨fun p _ h => marginalPatternProb_lt S p h,
    fun p _ _ h' h'' => marginalPatternProb_eq_of_ne S p h' h'',
    fun _ hx => ⟨fun p _ h => ismlLikelihood_lt hx p h, fun _ _ h => h.eq hx⟩⟩

end MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent.SitePatterns
