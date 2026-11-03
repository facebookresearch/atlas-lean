/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Configuration.CylinderDeriv

/-!
# Tests for `MathlibExt.Probability.Configuration.CylinderDeriv`

Witness: the increasing event `A = {ω | ω 0 = true}` ("site `0` is open"), on `ℕ` and on `Fin 2`.

* `StatMech.extendOff`: evaluated inside and outside the finite set.
* `StatMech.realSingleton_eq_configWeight`, `StatMech.finiteRealProb_eq_prob`: on `Fin 2` the
  mass of `⊤` is `p²` and `P(A) = p`.
* `StatMech.realProb_cylinder_eq_prob`: the `DependsOn` hypothesis is proved for `A` on `ℕ` with
  `F = {0}`, and the theorem is applied.
* `StatMech.hasDerivAt_realProb_cylinder_pivotal`, `StatMech.deriv_realProb_cylinder_pivotal`
  (Russo's formula): `IsIncreasing A` is proved and both are applied.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Configuration.CylinderDeriv

open MeasureTheory NNReal
open _root_.StatMech

/-- `extendOff F ω η` agrees with `η` on `F` and with `ω` off `F`. -/
example (η : ConfigSpace ↥({0} : Finset ℕ)) :
    extendOff {0} (⊥ : ConfigSpace ℕ) η 0 = η ⟨0, by simp⟩ ∧
      extendOff {0} (⊥ : ConfigSpace ℕ) η 1 = false := by
  simp [extendOff]

/-- The event "site `0` is open". -/
def siteOpen (E : Type*) (e : E) : Set (ConfigSpace E) := {ω | ω e = true}

/-- "Site `e` is open" is an increasing event. -/
lemma isIncreasing_siteOpen {E : Type*} (e : E) : IsIncreasing (siteOpen E e) :=
  fun _ b hab ha => by
    simp only [siteOpen, Set.mem_ofPred_eq] at ha ⊢
    have h := hab e
    rw [ha] at h
    exact le_antisymm (Bool.le_true _) h

/-- On `Fin 2`, the mass of `⊤` is `p²`. -/
example (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Fin 2) p hp).real {⊤} = (p : ℝ) ^ 2 := by
  rw [realSingleton_eq_configWeight]
  simp [configWeight, edgeWeight, sq]

/-- On `Fin 2`, `P(site 0 open) = p`. -/
example (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Fin 2) p hp).real (siteOpen (Fin 2) 0) = p := by
  rw [finiteRealProb_eq_prob]
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2))) =
      {![true, true], ![true, false], ![false, true], ![false, false]} := by decide
  simp only [prob, huniv]
  simp [siteOpen, Set.indicator, configWeight, edgeWeight, Fin.prod_univ_two]
  ring

/-- `siteOpen ℕ 0` depends only on the coordinate `0`. -/
lemma dependsOn_siteOpen :
    DependsOn ((siteOpen ℕ 0).indicator (fun _ => (1 : ℝ))) (({0} : Finset ℕ) : Set ℕ) := by
  intro x y h
  have h0 : x 0 = y 0 := h 0 (by simp)
  by_cases hy : y 0 = true <;> simp [Set.indicator, siteOpen, h0, hy]

/-- The probability of a cylinder event is the finite weight of its projection. -/
example (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := ℕ) p hp).real (siteOpen ℕ 0)
      = prob (p : ℝ) (({0} : Finset ℕ).restrict '' siteOpen ℕ 0) :=
  realProb_cylinder_eq_prob p hp _ _ dependsOn_siteOpen

/-- Russo's formula applied to the increasing event "site `0` is open". -/
example (q : ℝ) :
    HasDerivAt (fun q => prob q (({0} : Finset ℕ).restrict '' siteOpen ℕ 0))
      (∑ e : ↥({0} : Finset ℕ), pivotalProb q (({0} : Finset ℕ).restrict '' siteOpen ℕ 0) e)
      q :=
  hasDerivAt_realProb_cylinder_pivotal _ (isIncreasing_siteOpen 0) _ q

/-- Russo's formula in `deriv` form on `Fin 2` with `F = univ`. -/
example (q : ℝ) :
    deriv (fun q => prob q ((Finset.univ : Finset (Fin 2)).restrict '' siteOpen (Fin 2) 0)) q
      = ∑ e : ↥(Finset.univ : Finset (Fin 2)),
          pivotalProb q ((Finset.univ : Finset (Fin 2)).restrict '' siteOpen (Fin 2) 0) e :=
  deriv_realProb_cylinder_pivotal _ (isIncreasing_siteOpen 0) _ q

end MathlibExtTest.StatMech.Probability.Configuration.CylinderDeriv
