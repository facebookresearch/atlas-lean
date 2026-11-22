/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.BurgersFiniteTime

open Set
open scoped ContDiff
open ColeHopf

example {u : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x, u t x = burgersSolution ν (u 0) a t x :=
  eq_burgersSolution_finite hν hc hu hb hpde a

open Filter
open scoped Topology

-- Both endpoints are covered by interior-only PDE and smoothness assumptions.
example {u : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a x : ℝ) : u T x = burgersSolution ν (u 0) a T x :=
  eq_burgersSolution_finite hν hc hu hb hpde a T ⟨hT, le_rfl⟩ x

-- A zero-length lifespan requires no PDE or differentiability.
example {u : ℝ → ℝ → ℝ} (hc : Continuous (u 0))
    (hb : ∃ M, ∀ x, |u 0 x| ≤ M) (a x : ℝ) :
    u 0 x = burgersSolution 3 (u 0) a 0 x := by
  apply eq_burgersSolution_finite (T := 0) (by norm_num)
    (show ContinuousOn (Function.uncurry u) (Icc 0 0 ×ˢ univ) from
      (hc.comp continuous_snd).continuousOn.congr (fun p hp => by
        have ht : p.1 = 0 := le_antisymm hp.1.2 hp.1.1
        simp only [Function.uncurry_def, Function.comp_apply, ht]))
    (by simp only [Ioo_self, empty_prod]; exact contDiffOn_empty)
    (by simpa only [Icc_self, mem_singleton_iff, forall_eq] using hb)
    (by simp only [Ioo_self, mem_empty_iff_false, false_implies, implies_true])
    a 0 ⟨le_rfl, le_rfl⟩ x

-- Outside values may differ on both sides of the lifespan.
private noncomputable def cut (u : ℝ → ℝ → ℝ) (T c t x : ℝ) : ℝ :=
  if t ∈ Icc 0 T then u t x else c

private theorem cut_continuous {u : ℝ → ℝ → ℝ} {T c : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)) :
    ContinuousOn (Function.uncurry (cut u T c)) (Icc 0 T ×ˢ univ) :=
  hc.congr (fun p hp => by simp [Function.uncurry_def, cut, hp.1])

private theorem cut_smooth {u : ℝ → ℝ → ℝ} {T c : ℝ}
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ)) :
    ContDiffOn ℝ 2 (Function.uncurry (cut u T c)) (Ioo 0 T ×ˢ univ) :=
  hu.congr (fun p hp => by simp [Function.uncurry_def, cut, hp.1.1.le, hp.1.2.le])

private theorem cut_burgers {u : ℝ → ℝ → ℝ} {ν T c t : ℝ} (ht : t ∈ Ioo 0 T)
    (hpde : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (x : ℝ) :
    deriv (fun s => cut u T c s x) t + cut u T c t x * deriv (cut u T c t) x =
      ν * iteratedDeriv 2 (cut u T c t) x := by
  have he : (fun s => cut u T c s x) =ᶠ[𝓝 t] (fun s => u s x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    simp [cut, hs.1.le, hs.2.le]
  have hx : cut u T c t = u t := funext (fun y => by simp [cut, ht.1.le, ht.2.le])
  rw [he.deriv_eq, hx]
  exact hpde x

private noncomputable def corner (x : ℝ) : ℝ := |Real.sin x|
private theorem corner_continuous : Continuous corner := Real.continuous_sin.abs
private theorem corner_bound (x : ℝ) : |corner x| ≤ 1 := by
  simpa only [corner, abs_abs] using Real.abs_sin_le_one x

-- Nonconstant, merely continuous initial data; arbitrary post-lifespan values.
example (c d t x : ℝ) (ht : t ∈ Icc 0 2) :
    cut (burgersSolution 3 corner 7) 2 c t x =
      cut (burgersSolution 3 corner (-4)) 2 d t x := by
  apply burgers_eq_finite (by norm_num : (0 : ℝ) < 3)
    (cut_continuous (burgersSolution_continuous_of_bounded
      corner_continuous ⟨1, corner_bound⟩ (by norm_num) 7).continuousOn)
    (cut_continuous (burgersSolution_continuous_of_bounded
      corner_continuous ⟨1, corner_bound⟩ (by norm_num) (-4)).continuousOn)
    (cut_smooth ((burgersSolution_contDiffOn_of_bounded
      corner_continuous ⟨1, corner_bound⟩ (by norm_num) 7).mono (fun _ hp => ⟨hp.1.1, hp.2⟩)))
    (cut_smooth ((burgersSolution_contDiffOn_of_bounded
      corner_continuous ⟨1, corner_bound⟩ (by norm_num) (-4)).mono (fun _ hp => ⟨hp.1.1, hp.2⟩)))
    ⟨1, fun s hs y => by simpa only [cut, ite_eq_left hs] using
      abs_burgersSolution_le corner_continuous (by norm_num) corner_bound 7 s y⟩
    ⟨1, fun s hs y => by simpa only [cut, ite_eq_left hs] using
      abs_burgersSolution_le corner_continuous (by norm_num) corner_bound (-4) s y⟩
    (fun s hs y => cut_burgers hs (fun z => burgersSolution_burgers_of_bounded
      corner_continuous ⟨1, corner_bound⟩ (by norm_num) 7 s z hs.1) y)
    (fun s hs y => cut_burgers hs (fun z => burgersSolution_burgers_of_bounded
      corner_continuous ⟨1, corner_bound⟩ (by norm_num) (-4) s z hs.1) y)
    _ t ht x
  intro y
  simp only [cut, show (0 : ℝ) ∈ Icc 0 2 by constructor <;> norm_num, ite_true,
    burgersSolution_zero corner_continuous (by norm_num : (3 : ℝ) ≠ 0)]

example : cut (fun _ _ => 2) 1 17 (-1) 0 ≠ cut (fun _ _ => 2) 1 (-11) (-1) 0 := by
  norm_num [cut]

example : cut (fun _ _ => 2) 1 17 2 0 ≠ cut (fun _ _ => 2) 1 (-11) 2 0 := by
  norm_num [cut]

-- Locality of the profile includes its normalization integral over the entire past strip.
example (u : ℝ → ℝ → ℝ) (ν a c T t x : ℝ) (ht : t ∈ Icc 0 T) :
    initialInverseProfile ν (cut u T c) a t x = initialInverseProfile ν u a t x := by
  exact initialInverseProfile_congrOn (fun p hp => by
    simp [Function.uncurry_def, cut, hp.1]) ν a ht x

example {u : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)) (ν a x : ℝ) :
    Tendsto (Function.uncurry (initialInverseProfile ν u a))
      (𝓝[Icc 0 T ×ˢ univ] (T, x)) (𝓝 (initialInverseProfile ν u a T x)) :=
  (initialInverseProfile_continuousOn_finite hT hc ν a (T, x) ⟨⟨hT, le_rfl⟩, mem_univ _⟩).tendsto

example {u : ℝ → ℝ → ℝ} {ν t T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ)) (ht : t ∈ Ioo 0 T)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a x : ℝ) :
    deriv (fun s => initialInverseProfile ν u a s x) t =
      ν * iteratedDeriv 2 (initialInverseProfile ν u a t) x :=
  (initialInverseProfile_hasDerivAt_heat_finite hc hu ht hb hν a x).deriv

-- Empty strips require no values or regularity.
example (u : ℝ → ℝ → ℝ) : ∀ t ∈ Icc 0 (-1 : ℝ), ∀ x,
    u t x = burgersSolution 3 (u 0) 5 t x := by
  apply eq_burgersSolution_finite (by norm_num)
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private noncomputable def terminalJump (t : ℝ) (_x : ℝ) : ℝ := if t < 1 then 0 else 1

-- Interior smoothness and the PDE do not suffice without continuity of the terminal trace.
example : ¬ ContinuousOn (Function.uncurry terminalJump) (Icc 0 1 ×ˢ univ) := by
  intro hc
  have hu : ContDiffOn ℝ 2 (Function.uncurry terminalJump) (Ioo 0 1 ×ˢ univ) :=
    (contDiffOn_const (c := (0 : ℝ))).congr (fun p hp => by
      simp [Function.uncurry_def, terminalJump, hp.1.2])
  have hpde (t : ℝ) (ht : t ∈ Ioo 0 1) (x : ℝ) :
      deriv (fun s => terminalJump s x) t + terminalJump t x * deriv (terminalJump t) x =
        3 * iteratedDeriv 2 (terminalJump t) x := by
    have he : (fun s => terminalJump s x) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      simp [terminalJump, show s < 1 from hs]
    have hx : terminalJump t = fun _ => (0 : ℝ) :=
      funext (fun _ => by simp [terminalJump, ht.2])
    rw [he.deriv_eq, hx]
    simp
  have hh := burgers_eq_finite (u := terminalJump) (v := fun _ _ => 0)
    (by norm_num : (0 : ℝ) < 3) hc continuousOn_const hu contDiffOn_const
    ⟨1, fun t _ x => by unfold terminalJump; split_ifs <;> norm_num⟩
    ⟨0, by intros; simp⟩ hpde (by intros; simp) (by intro x; norm_num [terminalJump])
  have h := hh 1 (by constructor <;> norm_num) 0
  norm_num [terminalJump] at h
