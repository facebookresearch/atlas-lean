/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ComplexAnalysis/FatouJulia.lean` (leanprover/lean-eval), problem
`fatou_julia_dichotomy`, at commit 38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/fatou_julia_dichotomy.toml`, rev 1, submitter Kim Morrison, status archived):
the definitions `Tc`, `Mandelbrot` and `FilledJulia` and the statement of
`julia_cantor_dichotomy`, with the docstrings and comments they had in the former wanted module
`WantedExt/Analysis/FatouJuliaWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Analysis.FatouJuliaWanted` namespace. Mathematical statements are unchanged. Later
change (ATLAS, 2026): the `theorem_wanted` was proved and the declarations moved from
`WantedExt/Analysis/FatouJuliaWanted.lean` to this `MathlibExt` module with unchanged names,
statements and docstrings, and the imports of `Batteries.Util.ProofWanted` and of all of Mathlib
were replaced by narrower Mathlib imports.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`julia_cantor_dichotomy`, the private declarations it uses and the module documentation.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.UniformSpace.UniformApproximation
import MathlibExt.Analysis.Complex.NormalFamilies

/-!
# Fatou–Julia / Cantor dichotomy

For the quadratic family `T_c(z) = z² + c`, the filled Julia set
`K_c = { z ∈ ℂ | T_c^n(z) stays bounded }` satisfies:

- `c ∈ M` (Mandelbrot set) implies `K_c` is connected;
- `c ∉ M` implies `K_c` is homeomorphic to the Cantor space `ℕ → Bool`.

For quadratic polynomials, the usual Julia set is `∂K_c`. The submitted
statement uses the filled Julia set `K_c`; this is equivalent for the
dichotomy here, since connectedness of `K_c` is equivalent to
connectedness of `∂K_c`, and in the escaping case `K_c = ∂K_c` is a
Cantor set.

The main result is `julia_cantor_dichotomy`, which proves both statements.

## Proof outline

* An orbit that leaves the closed disc of radius `r = max 2 ‖c‖` tends to infinity, so `K_c` is
  the set of points whose orbit stays in that disc. It is compact, it contains the fixed points
  of `T_c`, and `T_c z ∈ K_c` if and only if `z ∈ K_c`.
* If `A` is connected and contains the critical value `c`, then `T_c⁻¹(A)` is connected: `T_c`
  is open and closed, and `0` is the only preimage of `c`.
* If `c ∈ M`, then `c ∈ K_c`, and `K_c` is the decreasing intersection of the compact sets
  `(T_c^n)⁻¹(D)`, `D` the closed disc of radius `r`. They are connected by the previous point, and a
  decreasing intersection of compact connected sets is connected.
* If `c ∉ M`, let `N` be the first time with `r < ‖T_c^N(c)‖` and choose `r < R < ‖T_c^N(c)‖`.
  The open set `V = (T_c^N)⁻¹(B(0, R))` is connected, contains `K_c` and contains the closure of
  `T_c⁻¹(V)`.
* The set `{z | R < ‖T_c^N(z)‖}` is connected by the maximum modulus principle, and it contains
  `c` and all points of norm larger than `R`. Moving `p` inside it by small steps, a holomorphic
  square root of `z - p` on `V` passes from one `p` to the next (multiply by the principal
  branch of `√((z - q) / (z - p))`), so `√(z - c)` has a holomorphic branch `s` on `V`. The
  inverse branches `±s` of `T_c` map `V` into `T_c⁻¹(V)`.
* Coding: every `z ∈ K_c` is `s (T_c z)` or `-s (T_c z)`. Recording the sign along the orbit
  gives a continuous map `K_c → (ℕ → Bool)`. It is onto because the cylinders (images of `K_c`
  under compositions of inverse branches) are nested, compact and nonempty.
* It is injective because the cylinders shrink uniformly. Otherwise a König-type argument gives
  words `v (n + 1) = b n :: v n` whose compositions stay far from constant on `K_c`. Montel's
  theorem gives a non-constant limit `f` along a subsequence and a limit `ψ` of the connecting
  compositions with `ψ ∘ f = f`. By the open mapping and identity theorems `ψ` is the identity
  on `V`, although it maps `V` into the closure of `T_c⁻¹(V)`; then `V` would be clopen.
* A continuous bijection from a compact space onto a Hausdorff space is a homeomorphism.

## Implementation notes

The definitions `Tc`, `Mandelbrot` and `FilledJulia` and the statement keep the full names they
had in the former wanted module, so the namespace still reads `FatouJuliaWanted`. The shrinking
of the cylinders uses Montel's theorem
(`MathlibExt.Analysis.Complex.NormalFamilies.montel`) in place of the Poincaré metric of the
classical proof, so no Riemann map of a non-convex domain is needed.

## References

* P. Fatou, *Sur les équations fonctionnelles*, Bull. Soc. Math. France 47 (1919), 161-271; 48
  (1920), 33-94, 208-314. G. Julia, *Mémoire sur l'itération des fonctions rationnelles*, J. Math.
  Pures Appl. 1 (1918), 47-245. Modern statement: A. Douady and J. H. Hubbard, *Étude dynamique
  des polynômes complexes I, II*, Publ. Math. Orsay 84-02, 85-04. Listed as §62 (additional
  statement 1) in O. Knill, *Some Fundamental Theorems in Mathematics*. These are the sources
  cited by problem `fatou_julia_dichotomy` of the lean-eval benchmark (leanprover/lean-eval),
  from which the definitions and the statement are taken.
-/

@[expose] public section

namespace MathlibExt.Analysis.FatouJuliaWanted
namespace ComplexAnalysis
namespace FatouJuliaProblem

open Function

/-- **Quadratic map $T_c$.** For $c \in \mathbb{C}$, $T_c \colon \mathbb{C} \to \mathbb{C}$ is the
map $T_c(z) = z^2 + c$. -/
def Tc (c : ℂ) (z : ℂ) : ℂ := z ^ 2 + c

/-- **Mandelbrot set of the quadratic family.** Let $T_c(z) = z^2 + c$ for $c \in \mathbb{C}$
and let $T_c^n$ be its $n$-fold iterate. The Mandelbrot set $M$ is the set of $c \in \mathbb{C}$
for which the orbit of $0$ under $T_c$ is bounded: there is a real $R$ such that
$|T_c^n(0)| \le R$ for every $n \ge 0$. -/
def Mandelbrot : Set ℂ :=
  { c : ℂ | ∃ M : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ M }

/-- **Filled Julia set.** For $c \in \mathbb{C}$, let $T_c(z) = z^2 + c$ and let $T_c^n$ be its
$n$-fold iterate. The filled Julia set $K_c$ is the set of $z \in \mathbb{C}$ whose orbit under
$T_c$ is bounded: there is a real $M$ such that $|T_c^n(z)| \le M$ for every $n \ge 0$. -/
def FilledJulia (c : ℂ) : Set ℂ :=
  { z : ℂ | ∃ M : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] z‖ ≤ M }

section Proof

open Filter Topology Metric Set

/-- The escape radius `max 2 ‖c‖`. -/
private noncomputable def escR (c : ℂ) : ℝ := max 2 ‖c‖

private lemma two_le_escR (c : ℂ) : 2 ≤ escR c := le_max_left _ _

private lemma norm_le_escR (c : ℂ) : ‖c‖ ≤ escR c := le_max_right _ _

private lemma continuous_Tc (c : ℂ) : Continuous (Tc c) := by
  unfold Tc; fun_prop

private lemma differentiable_Tc (c : ℂ) : Differentiable ℂ (Tc c) := by
  unfold Tc; fun_prop

private lemma sq_sub_le_norm_Tc (c z : ℂ) : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tc c z‖ := by
  unfold Tc
  have h := norm_sub_le (z ^ 2 + c) c
  simp only [add_sub_cancel_right, norm_pow] at h
  linarith

private lemma escape_step {c z : ℂ} (hz : escR c ≤ ‖z‖) :
    escR c + 2 * (‖z‖ - escR c) ≤ ‖Tc c z‖ := by
  have h1 := sq_sub_le_norm_Tc c z
  have h2 := two_le_escR c
  have h3 := norm_le_escR c
  nlinarith [mul_nonneg (sub_nonneg.2 (h2.trans hz)) (norm_nonneg z)]

/-- Outside the disc of radius `escR c`, the distance to that disc at least doubles at each step. -/
private lemma escape_iter {c z : ℂ} (hz : escR c ≤ ‖z‖) (n : ℕ) :
    escR c + 2 ^ n * (‖z‖ - escR c) ≤ ‖(Tc c)^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']
    have h0 : 0 ≤ 2 ^ n * (‖z‖ - escR c) := mul_nonneg (by positivity) (by linarith)
    have hle : escR c ≤ ‖(Tc c)^[n] z‖ := by linarith
    have := escape_step hle
    have he : (2 : ℝ) ^ (n + 1) * (‖z‖ - escR c) = 2 * (2 ^ n * (‖z‖ - escR c)) := by ring
    linarith

private lemma norm_le_norm_iterate {c z : ℂ} (hz : escR c < ‖z‖) (n : ℕ) :
    ‖z‖ ≤ ‖(Tc c)^[n] z‖ := by
  have h := escape_iter hz.le n
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2 : 0 ≤ ‖z‖ - escR c := by linarith
  nlinarith

/-- `K_c` is the set of points whose orbit stays in the closed disc of radius `escR c`. -/
private lemma mem_filledJulia_iff {c z : ℂ} :
    z ∈ FilledJulia c ↔ ∀ n, ‖(Tc c)^[n] z‖ ≤ escR c := by
  constructor
  · rintro ⟨M, hM⟩ n
    by_contra h
    push Not at h
    have hpos : 0 < ‖(Tc c)^[n] z‖ - escR c := by linarith
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((M - escR c) / (‖(Tc c)^[n] z‖ - escR c))
      one_lt_two
    rw [div_lt_iff₀ hpos] at hk
    have := escape_iter h.le k
    rw [← iterate_add_apply] at this
    linarith [hM (k + n)]
  · intro h
    exact ⟨escR c, h⟩

private lemma isClosed_filledJulia (c : ℂ) : IsClosed (FilledJulia c) := by
  have : FilledJulia c = ⋂ n, (Tc c)^[n] ⁻¹' closedBall 0 (escR c) := by
    ext z
    simp [mem_filledJulia_iff]
  rw [this]
  exact isClosed_iInter fun n => isClosed_closedBall.preimage ((continuous_Tc c).iterate n)

private lemma filledJulia_subset (c : ℂ) : FilledJulia c ⊆ closedBall 0 (escR c) :=
  fun z hz => by simpa using mem_filledJulia_iff.1 hz 0

private lemma isCompact_filledJulia (c : ℂ) : IsCompact (FilledJulia c) :=
  isCompact_of_isClosed_isBounded (isClosed_filledJulia c)
    (isBounded_closedBall.subset (filledJulia_subset c))

/-- `K_c` is completely invariant: `T_c z ∈ K_c` if and only if `z ∈ K_c`. -/
private lemma Tc_mem_filledJulia_iff {c z : ℂ} :
    Tc c z ∈ FilledJulia c ↔ z ∈ FilledJulia c := by
  simp only [mem_filledJulia_iff]
  constructor
  · intro h n
    cases n with
    | zero =>
      simp only [iterate_zero, id_eq]
      by_contra h'
      push Not at h'
      have := escape_step h'.le
      have h0 := h 0
      simp only [iterate_zero, id_eq] at h0
      linarith
    | succ n =>
      rw [iterate_succ_apply]
      exact h n
  · intro h n
    rw [← iterate_succ_apply]
    exact h (n + 1)

private lemma iterate_mem_filledJulia {c z : ℂ} (hz : z ∈ FilledJulia c) (n : ℕ) :
    (Tc c)^[n] z ∈ FilledJulia c := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [iterate_succ_apply']
    exact Tc_mem_filledJulia_iff.2 ih

/-- `K_c` contains the fixed points of `T_c`. -/
private lemma filledJulia_nonempty (c : ℂ) : (FilledJulia c).Nonempty := by
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (discrim (1 : ℂ) (-1) c)
  obtain ⟨z, hz⟩ := exists_quadratic_eq_zero one_ne_zero ⟨s, hs⟩
  have hfix : Tc c z = z := by
    unfold Tc
    linear_combination hz
  refine ⟨z, ‖z‖, fun n => ?_⟩
  rw [iterate_fixed hfix]

/-! ## Connectedness -/

/-- `T_c` is an open map (open mapping theorem). -/
private lemma isOpenMap_Tc (c : ℂ) : IsOpenMap (Tc c) := by
  have h : AnalyticOnNhd ℂ (Tc c) univ :=
    (differentiable_Tc c).differentiableOn.analyticOnNhd isOpen_univ
  rcases h.is_constant_or_isOpenMap with ⟨w, hw⟩ | h
  · exfalso
    have h0 := hw 0
    have h1 := hw 1
    simp only [Tc] at h0 h1
    have : (1 : ℂ) = 0 := by linear_combination h1 - h0
    exact one_ne_zero this
  · exact h

/-- `T_c` is a closed map, being proper. -/
private lemma isClosedMap_Tc (c : ℂ) : IsClosedMap (Tc c) :=
  (Homeomorph.addRight c).isClosedMap.comp (isClosedMap_pow ℂ 2)

/-- If `A` is preconnected and contains the critical value `c`, then `T_c⁻¹(A)` is
preconnected: a clopen piece of `T_c⁻¹(A)` maps onto `A`, hence contains `0`. -/
private lemma isPreconnected_preimage_Tc {c : ℂ} {A : Set ℂ} (hA : IsPreconnected A)
    (hcA : c ∈ A) : IsPreconnected (Tc c ⁻¹' A) := by
  set S := Tc c ⁻¹' A with hSdef
  have h0S : (0 : ℂ) ∈ S := by simpa [S, Tc] using hcA
  have key : ∀ u v : Set ℂ, IsOpen u → IsOpen v → S ⊆ u ∪ v → S ∩ (u ∩ v) = ∅ →
      (S ∩ v).Nonempty → (0 : ℂ) ∈ v := by
    intro u v hu hv hSuv hdisj hSv
    have hX1 : A ∩ Tc c '' v ⊆ Tc c '' uᶜ := by
      rintro a ⟨haA, y, hyv, rfl⟩
      refine ⟨y, fun hyu => ?_, rfl⟩
      have : y ∈ S ∩ (u ∩ v) := ⟨haA, hyu, hyv⟩
      rw [hdisj] at this
      exact this
    have hX2 : A ∩ Tc c '' uᶜ ⊆ Tc c '' v := by
      rintro a ⟨haA, y, hyu, rfl⟩
      refine ⟨y, ?_, rfl⟩
      rcases hSuv haA with h | h
      · exact absurd h hyu
      · exact h
    have hAsub : A ⊆ Tc c '' uᶜ := by
      by_contra hns
      rw [not_subset] at hns
      obtain ⟨a, haA, ha⟩ := hns
      obtain ⟨y, hyS, hyv⟩ := hSv
      obtain ⟨b, hbA, hbv, hbu⟩ := hA (Tc c '' v) (Tc c '' uᶜ)ᶜ (isOpenMap_Tc c v hv)
        (isClosedMap_Tc c uᶜ hu.isClosed_compl).isOpen_compl
        (fun b hb => by
          by_cases h : b ∈ Tc c '' uᶜ
          · exact Or.inl (hX2 ⟨hb, h⟩)
          · exact Or.inr h)
        ⟨Tc c y, hyS, y, hyv, rfl⟩ ⟨a, haA, ha⟩
      exact hbu (hX1 ⟨hbA, hbv⟩)
    obtain ⟨y, hyu, hy⟩ := hAsub hcA
    have hy0 : y = 0 := by
      have : y ^ 2 = 0 := by simpa [Tc] using hy
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    subst hy0
    rcases hSuv h0S with h | h
    · exact absurd h hyu
    · exact h
  intro u v hu hv hSuv hSu hSv
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have h0v := key u v hu hv hSuv hne hSv
  have h0u := key v u hv hu (by rwa [union_comm]) (by rwa [inter_comm v u]) hSu
  have : (0 : ℂ) ∈ S ∩ (u ∩ v) := ⟨h0S, h0u, h0v⟩
  rw [hne] at this
  exact this

/-- A decreasing intersection of compact preconnected sets is preconnected. -/
private lemma isPreconnected_iInter_of_antitone {A : ℕ → Set ℂ} (hanti : Antitone A)
    (hc : ∀ n, IsCompact (A n)) (hp : ∀ n, IsPreconnected (A n)) :
    IsPreconnected (⋂ n, A n) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv hdisj
  have hIcl : IsClosed (⋂ n, A n) := isClosed_iInter fun n => (hc n).isClosed
  have hIc : IsCompact (⋂ n, A n) := (hc 0).of_isClosed_subset hIcl (iInter_subset _ 0)
  have hu' : IsCompact ((⋂ n, A n) ∩ u) := hIc.inter_right hu
  have hv' : IsCompact ((⋂ n, A n) ∩ v) := hIc.inter_right hv
  have hd : Disjoint ((⋂ n, A n) ∩ u) ((⋂ n, A n) ∩ v) := by
    rw [Set.disjoint_iff]
    rintro z ⟨⟨hzI, hzu⟩, -, hzv⟩
    have : z ∈ (⋂ n, A n) ∩ (u ∩ v) := ⟨hzI, hzu, hzv⟩
    rw [hdisj] at this
    exact this
  obtain ⟨U, V, hUo, hVo, huU, hvV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact hu' hv' hd
  have hIUV : (⋂ n, A n) ∩ (U ∪ V)ᶜ = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_union, not_or, mem_empty_iff_false,
      iff_false, not_and, not_not]
    intro hzI hzU
    rcases huv hzI with h | h
    · exact absurd (huU ⟨hzI, h⟩) hzU
    · exact hvV ⟨hzI, h⟩
  obtain ⟨n, hn⟩ := (hc 0).elim_directed_family_closed (fun n => A n ∩ (U ∪ V)ᶜ)
    (fun n => (hc n).isClosed.inter (hUo.union hVo).isClosed_compl)
    (by
      rw [Set.disjoint_iff]
      rintro z ⟨-, hz⟩
      have hz' : z ∈ (⋂ n, A n) ∩ (U ∪ V)ᶜ :=
        ⟨mem_iInter.2 fun n => (mem_iInter.1 hz n).1, (mem_iInter.1 hz 0).2⟩
      rw [hIUV] at hz'
      exact hz')
    (fun i j => ⟨max i j, inter_subset_inter_left _ (hanti (le_max_left i j)),
      inter_subset_inter_left _ (hanti (le_max_right i j))⟩)
  have hAn : A n ⊆ U ∪ V := by
    intro z hz
    by_contra hzc
    exact Set.disjoint_left.1 hn (hanti (Nat.zero_le n) hz) ⟨hz, hzc⟩
  rcases (hp n).subset_or_subset hUo hVo hUV hAn with h | h
  · left
    intro z hz
    rcases huv hz with h' | h'
    · exact h'
    · exact absurd (h (mem_iInter.1 hz n)) (Set.disjoint_right.1 hUV (hvV ⟨hz, h'⟩))
  · right
    intro z hz
    rcases huv hz with h' | h'
    · exact absurd (h (mem_iInter.1 hz n)) (Set.disjoint_left.1 hUV (huU ⟨hz, h'⟩))
    · exact h'

/-- The connected half of the dichotomy. -/
private lemma isConnected_filledJulia {c : ℂ} (hc : c ∈ Mandelbrot) :
    IsConnected (FilledJulia c) := by
  have h0 : (0 : ℂ) ∈ FilledJulia c := hc
  have hcK : c ∈ FilledJulia c := by
    have h := Tc_mem_filledJulia_iff.2 h0
    rwa [show Tc c 0 = c by simp [Tc]] at h
  refine ⟨filledJulia_nonempty c, ?_⟩
  set A : ℕ → Set ℂ := fun n => (Tc c)^[n] ⁻¹' closedBall 0 (escR c) with hA
  have hK : FilledJulia c = ⋂ n, A n := by
    ext z
    simp [A, mem_filledJulia_iff]
  have hstep : ∀ n, A (n + 1) = Tc c ⁻¹' A n := fun n => by
    ext z
    simp [A]
  have hsub : Tc c ⁻¹' closedBall 0 (escR c) ⊆ closedBall 0 (escR c) := by
    intro z hz
    simp only [mem_preimage, mem_closedBall, dist_zero_right] at hz ⊢
    by_contra h
    push Not at h
    have := escape_step h.le
    linarith
  have hanti : Antitone A := antitone_nat_of_succ_le fun n => by
    intro z hz
    simp only [A, mem_preimage, iterate_succ_apply'] at hz ⊢
    exact hsub hz
  have hcomp : ∀ n, IsCompact (A n) := fun n =>
    isCompact_of_isClosed_isBounded (isClosed_closedBall.preimage ((continuous_Tc c).iterate n))
      ((isBounded_closedBall (x := (0 : ℂ)) (r := escR c)).subset fun z hz => by
        have := hanti (Nat.zero_le n) hz
        simpa [A] using this)
  have hpre : ∀ n, IsPreconnected (A n) := by
    intro n
    induction n with
    | zero => simpa [A] using (convex_closedBall (0 : ℂ) (escR c)).isPreconnected
    | succ n ih =>
      rw [hstep]
      exact isPreconnected_preimage_Tc ih (by simpa [A] using mem_filledJulia_iff.1 hcK n)
  rw [hK]
  exact isPreconnected_iInter_of_antitone hanti hcomp hpre

/-! ## The escaping case: domains -/

/-- The open set `T_c^{-n}(B(0, R))`. -/
private noncomputable def Dom (c : ℂ) (R : ℝ) (n : ℕ) : Set ℂ := (Tc c)^[n] ⁻¹' ball 0 R

private lemma isOpen_Dom (c : ℂ) (R : ℝ) (n : ℕ) : IsOpen (Dom c R n) :=
  isOpen_ball.preimage ((continuous_Tc c).iterate n)

private lemma Dom_succ (c : ℂ) (R : ℝ) (n : ℕ) : Dom c R (n + 1) = Tc c ⁻¹' Dom c R n := by
  ext z
  simp [Dom]

/-- `T_c^{-n}(B(0, R))` lies in `B(0, R)`. -/
private lemma Dom_subset_ball {c : ℂ} {R : ℝ} (hR : escR c < R) (n : ℕ) :
    Dom c R n ⊆ ball 0 R := by
  intro z hz
  simp only [Dom, mem_preimage, mem_ball, dist_zero_right] at hz ⊢
  by_contra h
  push Not at h
  have := norm_le_norm_iterate (hR.trans_le h) n
  linarith

/-- The closure of `T_c^{-(n+1)}(B(0, R))` lies in `T_c^{-n}(B(0, R))`. -/
private lemma closure_Dom_succ_subset {c : ℂ} {R : ℝ} (hR : escR c < R) (n : ℕ) :
    closure (Dom c R (n + 1)) ⊆ Dom c R n := by
  have h1 : closure (Dom c R (n + 1)) ⊆ (Tc c)^[n + 1] ⁻¹' closedBall 0 R :=
    closure_minimal (preimage_mono ball_subset_closedBall)
      (isClosed_closedBall.preimage ((continuous_Tc c).iterate (n + 1)))
  refine h1.trans fun z hz => ?_
  simp only [Dom, mem_preimage, mem_closedBall, mem_ball, dist_zero_right,
    iterate_succ_apply'] at hz ⊢
  by_contra h
  push Not at h
  have := escape_step ((hR.trans_le h).le)
  linarith

private lemma Dom_succ_subset {c : ℂ} {R : ℝ} (hR : escR c < R) (n : ℕ) :
    Dom c R (n + 1) ⊆ Dom c R n :=
  subset_closure.trans (closure_Dom_succ_subset hR n)

private lemma filledJulia_subset_Dom {c : ℂ} {R : ℝ} (hR : escR c < R) (n : ℕ) :
    FilledJulia c ⊆ Dom c R n := fun z hz => by
  simpa [Dom] using (mem_filledJulia_iff.1 hz n).trans_lt hR

/-- `T_c^{-n}(B(0, R))` is preconnected while the critical value stays in `B(0, R)`. -/
private lemma isPreconnected_Dom {c : ℂ} {R : ℝ} (n : ℕ)
    (hcn : ∀ k < n, ‖(Tc c)^[k] c‖ < R) : IsPreconnected (Dom c R n) := by
  induction n with
  | zero => simpa [Dom] using (convex_ball (0 : ℂ) R).isPreconnected
  | succ n ih =>
    rw [Dom_succ]
    exact isPreconnected_preimage_Tc (ih fun k hk => hcn k (hk.trans (Nat.lt_succ_self n)))
      (by simpa [Dom] using hcn n (Nat.lt_succ_self n))

/-- The set of points escaping from `B(0, R)` after `N` steps is preconnected
(maximum modulus principle). -/
private lemma isPreconnected_escaping {c : ℂ} {R : ℝ} (hR : escR c < R) (N : ℕ) :
    IsPreconnected {z : ℂ | R < ‖(Tc c)^[N] z‖} := by
  set E := {z : ℂ | R < ‖(Tc c)^[N] z‖} with hEdef
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) ((two_le_escR c).trans hR.le)
  have hEo : IsOpen E := isOpen_lt continuous_const ((continuous_Tc c).iterate N).norm
  set A := {z : ℂ | R < ‖z‖} with hAdef
  have hAE : A ⊆ E := fun z hz => lt_of_lt_of_le hz (norm_le_norm_iterate (hR.trans hz) N)
  have hApre : IsPreconnected A := by
    have : A = (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) ''
        (Ioi R ×ˢ univ) := by
      ext z
      constructor
      · intro hz
        refine ⟨(‖z‖, Complex.arg z), ⟨hz, mem_univ _⟩, ?_⟩
        simp
      · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
        have hr' : R < r := hr
        simp only [A, mem_ofPred_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
        rwa [abs_of_pos (hR0.trans hr')]
    rw [this]
    exact (isPreconnected_Ioi.prod isPreconnected_univ).image _ (by fun_prop)
  have hpiece : ∀ W : Set ℂ, IsOpen W → W ⊆ E → W ⊆ closedBall 0 R →
      (∀ z ∈ frontier W, z ∉ E) → W = ∅ := by
    intro W hWo hWE hWb hfr
    by_contra hne
    obtain ⟨z0, hz0⟩ := nonempty_iff_ne_empty.2 hne
    have := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_closedBall.subset hWb)
      ((differentiable_Tc c).iterate N).diffContOnCl (C := R) (fun z hz => by
        have := hfr z hz
        simpa [E] using this) (subset_closure hz0)
    exact absurd (hWE hz0) (by simpa [E] using this)
  have hfr : ∀ P Q : Set ℂ, IsOpen P → IsOpen Q → Disjoint P Q → E ⊆ P ∪ Q →
      ∀ z ∈ frontier P, z ∉ E := by
    intro P Q hP hQ hPQ hEPQ z hz hzE
    have hzP : z ∉ P := fun h => (hP.frontier_eq ▸ hz).2 h
    rcases hEPQ hzE with h | h
    · exact hzP h
    · obtain ⟨w, hwQ, hwP⟩ := mem_closure_iff.1 (frontier_subset_closure hz) Q hQ h
      exact Set.disjoint_left.1 hPQ hwP hwQ
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hEuv hdisj
  have hu' : IsOpen (E ∩ u) := hEo.inter hu
  have hv' : IsOpen (E ∩ v) := hEo.inter hv
  have hdisj' : Disjoint (E ∩ u) (E ∩ v) := by
    rw [Set.disjoint_iff]
    rintro z ⟨⟨hzE, hzu⟩, -, hzv⟩
    have : z ∈ E ∩ (u ∩ v) := ⟨hzE, hzu, hzv⟩
    rw [hdisj] at this
    exact this
  have hEuv' : E ⊆ (E ∩ u) ∪ (E ∩ v) := fun z hz => by
    rcases hEuv hz with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  have hAuv : A ⊆ (E ∩ u) ∪ (E ∩ v) := hAE.trans hEuv'
  rcases hApre.subset_or_subset hu' hv' hdisj' hAuv with hA | hA
  · left
    intro z hzE
    by_contra hzu
    have hzv : z ∈ E ∩ v := ⟨hzE, (hEuv hzE).resolve_left hzu⟩
    have hW := hpiece (E ∩ v) hv' inter_subset_left
      (fun w hw => by
        by_contra hwb
        simp only [mem_closedBall, dist_zero_right, not_le] at hwb
        exact Set.disjoint_left.1 hdisj' (hA hwb) hw)
      (hfr (E ∩ v) (E ∩ u) hv' hu' hdisj'.symm (by rwa [union_comm]))
    rw [hW] at hzv
    exact hzv
  · right
    intro z hzE
    by_contra hzv
    have hzu : z ∈ E ∩ u := ⟨hzE, (hEuv hzE).resolve_right hzv⟩
    have hW := hpiece (E ∩ u) hu' inter_subset_left
      (fun w hw => by
        by_contra hwb
        simp only [mem_closedBall, dist_zero_right, not_le] at hwb
        exact Set.disjoint_left.1 hdisj' hw (hA hwb))
      (hfr (E ∩ u) (E ∩ v) hu' hv' hdisj' hEuv')
    rw [hW] at hzu
    exact hzu

/-- A holomorphic branch of `√(z - c)` on `T_c^{-N}(B(0, R))` when the critical value has left
`closedBall 0 R` after `N` steps. -/
private lemma exists_sqrt_on_Dom {c : ℂ} {R : ℝ} (hR : escR c < R) {N : ℕ}
    (hcN : R < ‖(Tc c)^[N] c‖) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (Dom c R N) ∧ ∀ z ∈ Dom c R N, s z ^ 2 = z - c := by
  set U := Dom c R N with hUdef
  set F := (Tc c)^[N] ⁻¹' closedBall 0 R with hFdef
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) ((two_le_escR c).trans hR.le)
  have hUF : U ⊆ F := preimage_mono ball_subset_closedBall
  have hFc : IsClosed F := isClosed_closedBall.preimage ((continuous_Tc c).iterate N)
  have hUball : U ⊆ ball 0 R := Dom_subset_ball hR N
  have hFne : F.Nonempty :=
    (filledJulia_nonempty c).mono ((filledJulia_subset_Dom hR N).trans hUF)
  set Ω := {p : ℂ | ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ U ∧ ∀ z ∈ U, σ z ^ 2 = z - p}
    with hΩdef
  -- the chain step: from a square root of `z - p` to one of `z - q`
  have step : ∀ p ∈ Ω, ∀ q : ℂ, (∀ z ∈ U, ‖q - p‖ < ‖z - p‖) → q ∈ Ω := by
    rintro p ⟨σ, hσd, hσ2⟩ q hq
    have hzp : ∀ z ∈ U, z - p ≠ 0 := fun z hz h => by
      have := hq z hz
      rw [h, norm_zero] at this
      exact (norm_nonneg _).not_gt this
    have hslit : ∀ z ∈ U, (z - q) / (z - p) ∈ Complex.slitPlane := by
      intro z hz
      have heq : (z - q) / (z - p) = 1 - (q - p) / (z - p) := by
        field_simp [hzp z hz]
        ring
      have hlt : ‖(q - p) / (z - p)‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.2 (hzp z hz))]
        exact hq z hz
      rw [heq, Complex.mem_slitPlane_iff]
      left
      have := Complex.abs_re_le_norm ((q - p) / (z - p))
      simp only [Complex.sub_re, Complex.one_re]
      linarith [le_abs_self ((q - p) / (z - p)).re]
    refine ⟨fun z => σ z * ((z - q) / (z - p)) ^ (2⁻¹ : ℂ), ?_, ?_⟩
    · intro z hz
      have h1 : DifferentiableAt ℂ (fun z : ℂ => (z - q) / (z - p)) z :=
        (differentiableAt_id.sub_const q).div (differentiableAt_id.sub_const p) (hzp z hz)
      have h2 := h1.cpow_const (c := (2⁻¹ : ℂ)) (hslit z hz)
      exact (hσd z hz).mul h2.differentiableWithinAt
    · intro z hz
      rw [mul_pow, Complex.cpow_ofNat_inv_pow, hσ2 z hz]
      field_simp [hzp z hz]
  -- a base point far away
  obtain ⟨b, hbdef⟩ : ∃ b : ℂ, b = ((R + 1 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hbnorm : ‖b‖ = R + 1 := by
    rw [hbdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hbnorm; linarith
  have hbΩ : b ∈ Ω := by
    have hslit : ∀ z ∈ U, 1 - z / b ∈ Complex.slitPlane := by
      intro z hz
      have hzR : ‖z‖ < R := by simpa using hUball hz
      have hlt : ‖z / b‖ < 1 := by
        rw [norm_div, hbnorm, div_lt_one (by linarith)]
        linarith
      rw [Complex.mem_slitPlane_iff]
      left
      have := Complex.abs_re_le_norm (z / b)
      simp only [Complex.sub_re, Complex.one_re]
      linarith [le_abs_self (z / b).re]
    refine ⟨fun z => (-b) ^ (2⁻¹ : ℂ) * (1 - z / b) ^ (2⁻¹ : ℂ), ?_, ?_⟩
    · intro z hz
      have h1 : DifferentiableAt ℂ (fun z : ℂ => 1 - z / b) z := by fun_prop
      have h2 := h1.cpow_const (c := (2⁻¹ : ℂ)) (hslit z hz)
      exact ((differentiableAt_const ((-b) ^ (2⁻¹ : ℂ))).mul h2).differentiableWithinAt
    · intro z hz
      rw [mul_pow, Complex.cpow_ofNat_inv_pow, Complex.cpow_ofNat_inv_pow]
      field_simp
      ring
  -- the clopen argument on the connected set `E = Fᶜ`
  set E := Fᶜ with hEdef
  have hEo : IsOpen E := hFc.isOpen_compl
  have hEpre : IsPreconnected E := by
    have : E = {z : ℂ | R < ‖(Tc c)^[N] z‖} := by
      ext z
      simp [E, F]
    rw [this]
    exact isPreconnected_escaping hR N
  have hpos : ∀ p ∈ E, 0 < infDist p F := fun p hp => (hFc.notMem_iff_infDist_pos hFne).1 hp
  have hU_dist : ∀ p, ∀ z ∈ U, infDist p F ≤ ‖z - p‖ := fun p z hz => by
    rw [← dist_eq_norm, dist_comm]
    exact infDist_le_dist_of_mem (hUF hz)
  have hopen1 : IsOpen (Ω ∩ E) := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨hpΩ, hpE⟩
    refine Filter.mem_of_superset (ball_mem_nhds p (hpos p hpE)) fun q hq => ⟨?_, ?_⟩
    · refine step p hpΩ q fun z hz => ?_
      calc ‖q - p‖ = dist q p := (dist_eq_norm q p).symm
        _ < infDist p F := hq
        _ ≤ ‖z - p‖ := hU_dist p z hz
    · intro hqF
      have h1 : infDist p F ≤ dist p q := infDist_le_dist_of_mem hqF
      have h2 : dist q p < infDist p F := hq
      rw [dist_comm] at h1
      linarith
  have hopen2 : IsOpen (E \ Ω) := by
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨hqE, hqΩ⟩
    refine Filter.mem_of_superset (ball_mem_nhds q (half_pos (hpos q hqE))) fun p hp => ⟨?_, ?_⟩
    · intro hpF
      have h1 : infDist q F ≤ dist q p := infDist_le_dist_of_mem hpF
      have h2 : dist p q < infDist q F / 2 := hp
      have h3 := hpos q hqE
      rw [dist_comm] at h1
      linarith
    · intro hpΩ
      refine hqΩ (step p hpΩ q fun z hz => ?_)
      have h1 := hU_dist q z hz
      have h2 : ‖q - p‖ < infDist q F / 2 := by
        rw [← dist_eq_norm, dist_comm]
        exact hp
      have h3 : ‖z - q‖ ≤ ‖z - p‖ + ‖p - q‖ := norm_sub_le_norm_sub_add_norm_sub z p q
      rw [norm_sub_rev p q] at h3
      have h4 := hpos q hqE
      linarith
  have hcover : E ⊆ (Ω ∩ E) ∪ (E \ Ω) := fun z hz => by
    by_cases h : z ∈ Ω
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨hz, h⟩
  have hdisj : Disjoint (Ω ∩ E) (E \ Ω) := by
    rw [Set.disjoint_iff]
    rintro z ⟨⟨hzΩ, -⟩, -, hzΩ'⟩
    exact hzΩ' hzΩ
  have hbE : b ∈ E := by
    simp only [E, F, mem_compl_iff, mem_preimage, mem_closedBall, dist_zero_right, not_le]
    have := norm_le_norm_iterate (z := b) (c := c) (by rw [hbnorm]; linarith) N
    linarith
  have hEΩ : E ⊆ Ω ∩ E :=
    hEpre.subset_left_of_subset_union hopen1 hopen2 hdisj hcover ⟨b, hbE, hbΩ, hbE⟩
  have hcE : c ∈ E := by
    simp only [E, F, mem_compl_iff, mem_preimage, mem_closedBall, dist_zero_right, not_le]
    exact hcN
  exact (hEΩ hcE).1

/-! ## The escaping case: inverse branches and coding -/

/-- Locally uniform convergence passes to subsequences. -/
private lemma tendstoLocallyUniformlyOn_comp_atTop {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop s) {g : ℕ → ℕ} (hg : Tendsto g atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => F (g n)) f atTop s :=
  fun u hu x hx => let ⟨t, ht, h'⟩ := h u hu x hx; ⟨t, ht, hg.eventually h'⟩

/-- The data of the escaping case: a radius `R`, the escape time `N` of the critical value and a
holomorphic branch `s` of `√(z - c)` on `T_c^{-N}(B(0, R))`. -/
private structure Setup (c : ℂ) where
  R : ℝ
  N : ℕ
  s : ℂ → ℂ
  hR : escR c < R
  hconn : IsPreconnected (Dom c R N)
  hs : DifferentiableOn ℂ s (Dom c R N)
  hs2 : ∀ z ∈ Dom c R N, s z ^ 2 = z - c
  hcK : c ∉ FilledJulia c

namespace Setup

variable {c : ℂ}

private noncomputable def V (S : Setup c) : Set ℂ := Dom c S.R S.N

private lemma isOpen_V (S : Setup c) : IsOpen S.V := isOpen_Dom _ _ _

private lemma R_pos (S : Setup c) : 0 < S.R :=
  lt_of_lt_of_le (by norm_num) ((two_le_escR c).trans S.hR.le)

private lemma V_subset_ball (S : Setup c) : S.V ⊆ ball 0 S.R := Dom_subset_ball S.hR _

private lemma K_subset_V (S : Setup c) : FilledJulia c ⊆ S.V := filledJulia_subset_Dom S.hR _

private lemma closure_subset_V (S : Setup c) : closure (Dom c S.R (S.N + 1)) ⊆ S.V :=
  closure_Dom_succ_subset S.hR _

private lemma zero_notMem_of (hcK : c ∉ FilledJulia c) : (0 : ℂ) ∉ FilledJulia c := fun h =>
  hcK (by
    have := Tc_mem_filledJulia_iff.2 h
    rwa [show Tc c 0 = c by simp [Tc]] at this)

/-- The two inverse branches `±s` of `T_c`. -/
private noncomputable def br (S : Setup c) (a : Bool) (z : ℂ) : ℂ := if a then -S.s z else S.s z

private lemma Tc_br (S : Setup c) (a : Bool) {z : ℂ} (hz : z ∈ S.V) : Tc c (S.br a z) = z := by
  have := S.hs2 z hz
  cases a <;> simp [br, Tc, this]

private lemma br_mem (S : Setup c) (a : Bool) {z : ℂ} (hz : z ∈ S.V) :
    S.br a z ∈ Dom c S.R (S.N + 1) := by
  rw [Dom_succ, mem_preimage, S.Tc_br a hz]
  exact hz

private lemma br_mem_V (S : Setup c) (a : Bool) {z : ℂ} (hz : z ∈ S.V) : S.br a z ∈ S.V :=
  Dom_succ_subset S.hR _ (S.br_mem a hz)

private lemma differentiableOn_br (S : Setup c) (a : Bool) : DifferentiableOn ℂ (S.br a) S.V := by
  cases a
  · exact S.hs.congr fun z _ => by simp [br]
  · exact S.hs.neg.congr fun z _ => by simp [br]

private lemma br_mem_K (S : Setup c) (a : Bool) {z : ℂ} (hz : z ∈ FilledJulia c) :
    S.br a z ∈ FilledJulia c := by
  rw [← Tc_mem_filledJulia_iff, S.Tc_br a (S.K_subset_V hz)]
  exact hz

/-- Compositions of inverse branches: `G [a₀, …, aₙ₋₁] = br a₀ ∘ ⋯ ∘ br aₙ₋₁`. -/
private noncomputable def G (S : Setup c) : List Bool → ℂ → ℂ
  | [] => fun z => z
  | a :: w => fun z => S.br a (S.G w z)

private lemma G_nil (S : Setup c) (z : ℂ) : S.G [] z = z := rfl

private lemma G_cons (S : Setup c) (a : Bool) (w : List Bool) (z : ℂ) :
    S.G (a :: w) z = S.br a (S.G w z) :=
  rfl

private lemma G_append (S : Setup c) (u v : List Bool) (z : ℂ) :
    S.G (u ++ v) z = S.G u (S.G v z) := by
  induction u with
  | nil => rfl
  | cons a u ih => rw [List.cons_append, G_cons, G_cons, ih]

private lemma G_mem_V (S : Setup c) (w : List Bool) {z : ℂ} (hz : z ∈ S.V) : S.G w z ∈ S.V := by
  induction w with
  | nil => exact hz
  | cons a w ih => exact S.br_mem_V a ih

private lemma G_mem_Dom_succ (S : Setup c) {w : List Bool} (hw : w ≠ []) {z : ℂ} (hz : z ∈ S.V) :
    S.G w z ∈ Dom c S.R (S.N + 1) := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a w => exact S.br_mem a (S.G_mem_V w hz)

private lemma G_mem_K (S : Setup c) (w : List Bool) {z : ℂ} (hz : z ∈ FilledJulia c) :
    S.G w z ∈ FilledJulia c := by
  induction w with
  | nil => exact hz
  | cons a w ih => exact S.br_mem_K a ih

private lemma differentiableOn_G (S : Setup c) (w : List Bool) :
    DifferentiableOn ℂ (S.G w) S.V := by
  induction w with
  | nil => exact differentiableOn_id
  | cons a w ih => exact (S.differentiableOn_br a).comp ih fun z hz => S.G_mem_V w hz

private lemma norm_G_le (S : Setup c) (w : List Bool) {z : ℂ} (hz : z ∈ S.V) : ‖S.G w z‖ ≤ S.R := by
  have := S.V_subset_ball (S.G_mem_V w hz)
  simp only [mem_ball, dist_zero_right] at this
  exact this.le

/-- Limits of compositions of at least one inverse branch map `V` into the closure of
`T_c⁻¹(V)`. -/
private lemma limit_mem (S : Setup c) (W : ℕ → List Bool) {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun k => S.G (W k)) g atTop S.V)
    (hW : ∀ᶠ k in atTop, W k ≠ []) {z : ℂ} (hz : z ∈ S.V) :
    g z ∈ closure (Dom c S.R (S.N + 1)) :=
  mem_closure_of_tendsto (hconv.tendsto_at hz) (hW.mono fun _ hk => S.G_mem_Dom_succ hk hz)

/-- The cylinders of the coding shrink uniformly. -/
private lemma shrink (S : Setup c) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∀ w : List Bool, n ≤ w.length → ∀ x ∈ FilledJulia c, ∀ y ∈ FilledJulia c,
      ‖S.G w x - S.G w y‖ ≤ ε := by
  by_contra hcon
  push Not at hcon
  let Bad : List Bool → Prop := fun w =>
    ∃ x ∈ FilledJulia c, ∃ y ∈ FilledJulia c, ε < ‖S.G w x - S.G w y‖
  let Q : List Bool → Prop := fun v => ∀ m : ℕ, ∃ u : List Bool, m ≤ u.length ∧ Bad (u ++ v)
  have hQ0 : Q [] := fun m => by
    obtain ⟨w, hw, hbad⟩ := hcon m
    exact ⟨w, hw, by simpa using hbad⟩
  have hQstep : ∀ v, Q v → ∃ b : Bool, Q (b :: v) := by
    intro v hv
    by_contra hno
    push Not at hno
    have hno' : ∀ b : Bool, ∃ m : ℕ, ∀ u : List Bool, m ≤ u.length → ¬Bad (u ++ b :: v) := by
      intro b
      have := hno b
      simp only [Q, not_forall, not_exists, not_and] at this
      exact this
    obtain ⟨m1, hm1⟩ := hno' true
    obtain ⟨m2, hm2⟩ := hno' false
    obtain ⟨u, hu, hbad⟩ := hv (max m1 m2 + 1)
    rcases List.eq_nil_or_concat u with h | ⟨u', b, rfl⟩
    · subst h
      simp at hu
    · have hlen : max m1 m2 ≤ u'.length := by
        simp only [List.concat_eq_append, List.length_append, List.length_singleton] at hu
        omega
      rw [List.concat_eq_append, List.append_assoc, List.singleton_append] at hbad
      cases b
      · exact hm2 u' ((le_max_right _ _).trans hlen) hbad
      · exact hm1 u' ((le_max_left _ _).trans hlen) hbad
  choose bf hbf using hQstep
  let step : {v // Q v} → {v // Q v} := fun p => ⟨bf p.1 p.2 :: p.1, hbf p.1 p.2⟩
  let Vs : ℕ → List Bool := fun n => (step^[n] ⟨[], hQ0⟩).1
  have hVsQ : ∀ n, Q (Vs n) := fun n => (step^[n] ⟨[], hQ0⟩).2
  have hVs_succ : ∀ n, ∃ b, Vs (n + 1) = b :: Vs n := fun n =>
    ⟨_, by simp only [Vs, iterate_succ_apply']; rfl⟩
  have hVs_le : ∀ n m, n ≤ m → ∃ u, Vs m = u ++ Vs n := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨[], rfl⟩
    | succ m _ ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨b, hb⟩ := hVs_succ m
      exact ⟨b :: u, by rw [hb, hu]; rfl⟩
  have hVs_lt : ∀ n m, n < m → ∃ u, u ≠ [] ∧ Vs m = u ++ Vs n := by
    intro n m hnm
    obtain ⟨u, hu⟩ := hVs_le (n + 1) m hnm
    obtain ⟨b, hb⟩ := hVs_succ n
    exact ⟨u ++ [b], by simp, by rw [hu, hb]; simp⟩
  have hVs_ne : ∀ n, 0 < n → Vs n ≠ [] := by
    intro n hn
    obtain ⟨u, hu, h⟩ := hVs_lt 0 n hn
    rw [h]
    exact fun h' => hu (List.append_eq_nil_iff.1 h').1
  have hR0 := S.R_pos
  have hbound : ∀ W : ℕ → List Bool,
      MathlibExt.Analysis.Complex.NormalFamilies.IsLocallyUniformlyBoundedOn S.V
        (fun k => S.G (W k)) := fun W =>
    MathlibExt.Analysis.Complex.NormalFamilies.isLocallyUniformlyBoundedOn_of_forall_norm_le
      S.isOpen_V hR0.le fun k z hz => S.norm_G_le _ hz
  -- Montel: a subsequence of the coherent branches converges
  obtain ⟨φ, hφ, f, hfd, hfconv⟩ := MathlibExt.Analysis.Complex.NormalFamilies.montel S.isOpen_V
    (fun k => S.G (Vs k)) (fun k => S.differentiableOn_G _) (hbound Vs)
  have hfV : ∀ z ∈ S.V, f z ∈ S.V := fun z hz =>
    S.closure_subset_V (S.limit_mem (fun n => Vs (φ n)) hfconv
      ((eventually_ge_atTop 1).mono fun k hk =>
        hVs_ne _ (lt_of_lt_of_le zero_lt_one (hk.trans (hφ.id_le k)))) hz)
  -- the limit is not constant
  choose u hu x hx y hy hxy using fun k => hVsQ (φ k) 0
  obtain ⟨θ, hθ, χ, hχd, hχconv⟩ := MathlibExt.Analysis.Complex.NormalFamilies.montel
    S.isOpen_V (fun k => S.G (u k)) (fun k => S.differentiableOn_G _) (hbound u)
  have hK2 : IsCompact (FilledJulia c ×ˢ FilledJulia c) :=
    (isCompact_filledJulia c).prod (isCompact_filledJulia c)
  obtain ⟨⟨x0, y0⟩, ⟨hx0, hy0⟩, ζ, hζ, hxy0⟩ :=
    hK2.tendsto_subseq (x := fun j => (x (θ j), y (θ j))) fun j => ⟨hx _, hy _⟩
  have hx' : Tendsto (fun j => x (θ (ζ j))) atTop (𝓝 x0) :=
    (continuous_fst.tendsto _).comp hxy0
  have hy' : Tendsto (fun j => y (θ (ζ j))) atTop (𝓝 y0) :=
    (continuous_snd.tendsto _).comp hxy0
  have hconv1 : TendstoLocallyUniformlyOn (fun j => S.G (Vs (φ (θ (ζ j))))) f atTop S.V :=
    tendstoLocallyUniformlyOn_comp_atTop hfconv (hθ.comp hζ).tendsto_atTop
  have hconv2 : TendstoLocallyUniformlyOn (fun j => S.G (u (θ (ζ j)))) χ atTop S.V :=
    tendstoLocallyUniformlyOn_comp_atTop hχconv hζ.tendsto_atTop
  have hlim : ∀ (p : ℕ → ℂ) (p0 : ℂ), p0 ∈ FilledJulia c → (∀ j, p j ∈ FilledJulia c) →
      Tendsto p atTop (𝓝 p0) →
      Tendsto (fun j => S.G (u (θ (ζ j))) (S.G (Vs (φ (θ (ζ j)))) (p j))) atTop
        (𝓝 (χ (f p0))) := by
    intro p p0 hp0 hp hpt
    have hp0V := S.K_subset_V hp0
    have h1 : Tendsto (fun j => S.G (Vs (φ (θ (ζ j)))) (p j)) atTop (𝓝 (f p0)) :=
      hconv1.tendsto_comp (hfd.continuousOn.continuousWithinAt hp0V) hp0V
        (tendsto_nhdsWithin_iff.2 ⟨hpt, Eventually.of_forall fun j => S.K_subset_V (hp j)⟩)
    exact hconv2.tendsto_comp (hχd.continuousOn.continuousWithinAt (hfV p0 hp0V))
      (hfV p0 hp0V) (tendsto_nhdsWithin_iff.2
        ⟨h1, Eventually.of_forall fun j => S.G_mem_V _ (S.K_subset_V (hp j))⟩)
  have hge : ε ≤ ‖χ (f x0) - χ (f y0)‖ := by
    refine ge_of_tendsto ((hlim _ x0 hx0 (fun j => hx _) hx').sub
      (hlim _ y0 hy0 (fun j => hy _) hy')).norm (Eventually.of_forall fun j => ?_)
    have := hxy (θ (ζ j))
    rw [S.G_append, S.G_append] at this
    exact this.le
  have hfne : f x0 ≠ f y0 := fun h => by
    rw [h, sub_self, norm_zero] at hge
    linarith
  -- open mapping theorem
  have hfopen : IsOpen (f '' S.V) := by
    rcases (hfd.analyticOnNhd S.isOpen_V).is_constant_or_isOpen S.hconn with ⟨w, hw⟩ | h
    · exact absurd ((hw x0 (S.K_subset_V hx0)).trans (hw y0 (S.K_subset_V hy0)).symm) hfne
    · exact h S.V subset_rfl S.isOpen_V
  -- the connecting branches converge to the identity
  choose u' hu'ne hu'eq using fun k => hVs_lt (φ k) (φ (k + 1)) (hφ (Nat.lt_succ_self k))
  obtain ⟨θ', hθ', ψ, hψd, hψconv⟩ := MathlibExt.Analysis.Complex.NormalFamilies.montel
    S.isOpen_V (fun k => S.G (u' k)) (fun k => S.differentiableOn_G _) (hbound u')
  have hψf : ∀ z ∈ S.V, ψ (f z) = f z := by
    intro z hz
    have h1 : Tendsto (fun j => S.G (Vs (φ (θ' j + 1))) z) atTop (𝓝 (f z)) :=
      (hfconv.tendsto_at hz).comp ((tendsto_add_atTop_nat 1).comp hθ'.tendsto_atTop)
    have h2 : Tendsto (fun j => S.G (u' (θ' j)) (S.G (Vs (φ (θ' j))) z)) atTop
        (𝓝 (ψ (f z))) :=
      hψconv.tendsto_comp (hψd.continuousOn.continuousWithinAt (hfV z hz)) (hfV z hz)
        (tendsto_nhdsWithin_iff.2 ⟨(hfconv.tendsto_at hz).comp hθ'.tendsto_atTop,
          Eventually.of_forall fun j => S.G_mem_V _ hz⟩)
    have h3 : (fun j => S.G (Vs (φ (θ' j + 1))) z) =
        fun j => S.G (u' (θ' j)) (S.G (Vs (φ (θ' j))) z) := by
      funext j
      rw [hu'eq, S.G_append]
    rw [h3] at h1
    exact tendsto_nhds_unique h2 h1
  obtain ⟨z0, hz0⟩ := filledJulia_nonempty c
  have hz0V := S.K_subset_V hz0
  have hEq : EqOn ψ id S.V := by
    refine (hψd.analyticOnNhd S.isOpen_V).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id
      S.hconn (hfV z0 hz0V) ?_
    filter_upwards [hfopen.mem_nhds (mem_image_of_mem f hz0V)] with w hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact hψf z hz
  have hψmem : ∀ z ∈ S.V, ψ z ∈ closure (Dom c S.R (S.N + 1)) := fun z hz =>
    S.limit_mem (fun j => u' (θ' j)) hψconv (Eventually.of_forall fun j => hu'ne _) hz
  have hVcl : IsClosed S.V := by
    have : S.V = closure (Dom c S.R (S.N + 1)) := by
      refine Subset.antisymm (fun z hz => ?_) S.closure_subset_V
      have := hψmem z hz
      rwa [hEq hz] at this
    rw [this]
    exact isClosed_closure
  rcases isClopen_iff.1 ⟨hVcl, S.isOpen_V⟩ with h | h
  · rw [h] at hz0V
    exact hz0V
  · have hR' : ((S.R : ℝ) : ℂ) ∈ S.V := h ▸ mem_univ _
    have := S.V_subset_ball hR'
    simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR0] at this
    exact lt_irrefl _ this

open Classical in
/-- The symbol of a point: `true` when `z = -s(T_c z)`. -/
private noncomputable def bit (S : Setup c) (z : ℂ) : Bool :=
  if z + S.s (Tc c z) = 0 then true else false

private lemma sq_s_Tc (S : Setup c) {z : ℂ} (hz : z ∈ FilledJulia c) :
    S.s (Tc c z) ^ 2 = z ^ 2 := by
  rw [S.hs2 _ (S.K_subset_V (Tc_mem_filledJulia_iff.2 hz))]
  simp [Tc]

private lemma br_bit (S : Setup c) {z : ℂ} (hz : z ∈ FilledJulia c) :
    S.br (S.bit z) (Tc c z) = z := by
  by_cases h : z + S.s (Tc c z) = 0
  · simp only [bit, br, h, ↓reduceIte]
    linear_combination -h
  · simp only [bit, br, h, ↓reduceIte, Bool.false_eq_true]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (S.sq_s_Tc hz) with h' | h'
    · exact h'
    · exact absurd (by rw [h']; ring) h

private lemma bit_br (S : Setup c) (a : Bool) {z : ℂ} (hz : z ∈ FilledJulia c) :
    S.bit (S.br a z) = a := by
  have hzV := S.K_subset_V hz
  have hs0 : S.s z ≠ 0 := by
    intro h
    have h2 := S.hs2 z hzV
    rw [h] at h2
    have hzc : z = c := by linear_combination -h2
    exact S.hcK (hzc ▸ hz)
  unfold bit
  rw [S.Tc_br a hzV]
  cases a
  · have hne : ¬S.br false z + S.s z = 0 := by
      simp only [br, Bool.false_eq_true, ↓reduceIte]
      intro h
      apply hs0
      linear_combination h / 2
    simp only [hne, ↓reduceIte]
  · have heq : S.br true z + S.s z = 0 := by simp [br]
    simp only [heq, ↓reduceIte]

/-- The symbol is locally constant on `K_c`, since `0 ∉ K_c`. -/
private lemma continuousOn_bit (S : Setup c) : ContinuousOn S.bit (FilledJulia c) := by
  intro z hz
  have hmaps : MapsTo (Tc c) (FilledJulia c) S.V := fun y hy =>
    S.K_subset_V (Tc_mem_filledJulia_iff.2 hy)
  have hcont : ContinuousOn (fun y => S.s (Tc c y)) (FilledJulia c) :=
    S.hs.continuousOn.comp (continuous_Tc c).continuousOn hmaps
  have hz0 : z ≠ 0 := fun h => zero_notMem_of S.hcK (h ▸ hz)
  rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
  by_cases h : z + S.s (Tc c z) = 0
  · have hne : z - S.s (Tc c z) ≠ 0 := by
      intro h'
      apply hz0
      linear_combination (h + h') / 2
    have hc1 : ContinuousWithinAt (fun y => y - S.s (Tc c y)) (FilledJulia c) z :=
      continuousWithinAt_id.sub (hcont z hz)
    filter_upwards [hc1.eventually_ne hne, self_mem_nhdsWithin] with y hy hyK
    have hy' : y + S.s (Tc c y) = 0 := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (S.sq_s_Tc hyK) with h' | h'
      · exact absurd (by rw [h']; ring) hy
      · rw [h']
        ring
    simp only [bit, hy', h, ↓reduceIte]
  · have hc1 : ContinuousWithinAt (fun y => y + S.s (Tc c y)) (FilledJulia c) z :=
      continuousWithinAt_id.add (hcont z hz)
    filter_upwards [hc1.eventually_ne h] with y hy
    simp only [bit, hy, h, ↓reduceIte]

/-- The first `n` symbols of the itinerary of `x`. -/
private noncomputable def itin (S : Setup c) (x : ℂ) (n : ℕ) : List Bool :=
  List.ofFn fun j : Fin n => S.bit ((Tc c)^[j] x)

private lemma itin_succ (S : Setup c) (x : ℂ) (n : ℕ) :
    S.itin x (n + 1) = S.bit x :: S.itin (Tc c x) n := by
  simp only [itin, List.ofFn_succ, Fin.val_zero, iterate_zero, id_eq, Fin.val_succ,
    iterate_succ_apply]

/-- A point of `K_c` is recovered from its `n`-th image and its first `n` symbols. -/
private lemma G_itin (S : Setup c) {x : ℂ} (hx : x ∈ FilledJulia c) (n : ℕ) :
    S.G (S.itin x n) ((Tc c)^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [S.itin_succ, G_cons, iterate_succ_apply, ih (Tc_mem_filledJulia_iff.2 hx), S.br_bit hx]

/-- The image of a point of `K_c` under `G w` has itinerary starting with `w`. -/
private lemma itin_G (S : Setup c) (w : List Bool) {z : ℂ} (hz : z ∈ FilledJulia c) :
    S.itin (S.G w z) w.length = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.length_cons, S.itin_succ, G_cons, S.Tc_br a (S.K_subset_V (S.G_mem_K w hz)), ih,
      S.bit_br a (S.G_mem_K w hz)]

/-- The escaping half of the dichotomy: the itinerary map is a homeomorphism. -/
private lemma nonempty_homeomorph (S : Setup c) : Nonempty (FilledJulia c ≃ₜ (ℕ → Bool)) := by
  have : CompactSpace (FilledJulia c) := isCompact_iff_compactSpace.1 (isCompact_filledJulia c)
  let ι : FilledJulia c → (ℕ → Bool) := fun x n => S.bit ((Tc c)^[n] x)
  have hcont : Continuous ι := by
    refine continuous_pi fun n => ?_
    exact S.continuousOn_bit.comp_continuous
      (((continuous_Tc c).iterate n).comp continuous_subtype_val)
      fun x => iterate_mem_filledJulia x.2 n
  have hinj : Injective ι := by
    intro x y hxy
    apply Subtype.ext
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨n, hn⟩ := S.shrink ε hε
    have hw : S.itin x n = S.itin y n := by
      simp only [itin]
      congr 1
      funext j
      exact congrFun hxy j
    have hlen : (S.itin (x : ℂ) n).length = n := List.length_ofFn
    rw [dist_eq_norm, ← S.G_itin x.2 n, ← S.G_itin y.2 n, ← hw]
    exact hn _ hlen.ge _ (iterate_mem_filledJulia x.2 n) _ (iterate_mem_filledJulia y.2 n)
  have hsurj : Surjective ι := by
    intro a
    let C : ℕ → Set ℂ := fun n => S.G (List.ofFn fun j : Fin n => a j) '' FilledJulia c
    have hCc : ∀ n, IsCompact (C n) := fun n =>
      (isCompact_filledJulia c).image_of_continuousOn
        ((S.differentiableOn_G _).continuousOn.mono S.K_subset_V)
    have hCne : ∀ n, (C n).Nonempty := fun n => (filledJulia_nonempty c).image _
    have hCsub : ∀ n, C (n + 1) ⊆ C n := by
      rintro n _ ⟨z, hz, rfl⟩
      refine ⟨S.br (a n) z, S.br_mem_K _ hz, ?_⟩
      rw [List.ofFn_succ', List.concat_eq_append, S.G_append]
      rfl
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCsub
      hCne (hCc 0) fun n => (hCc n).isClosed
    have hxK : x ∈ FilledJulia c := by
      obtain ⟨z, hz, rfl⟩ := mem_iInter.1 hx 0
      exact hz
    refine ⟨⟨x, hxK⟩, funext fun n => ?_⟩
    obtain ⟨z, hz, hzx⟩ := mem_iInter.1 hx (n + 1)
    have h := S.itin_G (List.ofFn fun j : Fin (n + 1) => a j) hz
    rw [hzx, List.length_ofFn] at h
    exact congrFun (List.ofFn_inj.1 h) (Fin.last n)
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ι ⟨hinj, hsurj⟩) hcont⟩

end Setup

end Proof

/- **Fatou–Julia dichotomy.** For the quadratic family, `c ∈ M` implies
the filled Julia set `K_c` is connected; `c ∉ M` implies `K_c` is
homeomorphic to the Cantor space `ℕ → Bool`. -/
/-- **Fatou–Julia dichotomy for quadratic polynomials.** For $c \in \mathbb{C}$, let $K_c$ be the
filled Julia set of $T_c(z) = z^2 + c$ and let $M$ be the Mandelbrot set. If $c \in M$, then $K_c$
is nonempty and connected. If $c \notin M$, then $K_c$ is homeomorphic to the Cantor space
$\{0, 1\}^{\mathbb{N}}$ of binary sequences with the product topology.

Source: P. Fatou, *Sur les équations fonctionnelles*, Bull. Soc. Math. France 47 (1919), 161-271; 48
(1920), 33-94, 208-314. G. Julia, *Mémoire sur l'itération des fonctions rationnelles*, J. Math.
Pures Appl. 1 (1918), 47-245. Modern statement: A. Douady and J. H. Hubbard, *Étude dynamique des
polynômes complexes I, II*, Publ. Math. Orsay 84-02, 85-04. Listed as §62 (additional statement 1)
in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `fatou_julia_dichotomy`. -/
theorem julia_cantor_dichotomy (c : ℂ) :
    (c ∈ Mandelbrot → IsConnected (FilledJulia c)) ∧
    (c ∉ Mandelbrot → Nonempty ((FilledJulia c) ≃ₜ (ℕ → Bool))) := by
  refine ⟨isConnected_filledJulia, fun hc => ?_⟩
  have hcK : c ∉ FilledJulia c := by
    intro h
    have h1 : Tc c 0 ∈ FilledJulia c := by rwa [show Tc c 0 = c by simp [Tc]]
    have h0 : (0 : ℂ) ∈ FilledJulia c := Tc_mem_filledJulia_iff.1 h1
    exact hc h0
  have hex : ∃ n, escR c < ‖(Tc c)^[n] c‖ := by
    by_contra h
    push Not at h
    exact hcK (mem_filledJulia_iff.2 h)
  classical
  obtain ⟨N, hN, hlt⟩ : ∃ N, escR c < ‖(Tc c)^[N] c‖ ∧ ∀ k < N, ‖(Tc c)^[k] c‖ ≤ escR c :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_lt.1 (Nat.find_min hex hk)⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (escR c + ‖(Tc c)^[N] c‖) / 2 := ⟨_, rfl⟩
  have hR1 : escR c < R := by rw [hRdef]; linarith
  have hR2 : R < ‖(Tc c)^[N] c‖ := by rw [hRdef]; linarith
  obtain ⟨s, hs, hs2⟩ := exists_sqrt_on_Dom hR1 hR2
  exact Setup.nonempty_homeomorph
    ⟨R, N, s, hR1, isPreconnected_Dom N fun k hk => (hlt k hk).trans_lt hR1, hs, hs2, hcK⟩

end FatouJuliaProblem
end ComplexAnalysis

end MathlibExt.Analysis.FatouJuliaWanted
