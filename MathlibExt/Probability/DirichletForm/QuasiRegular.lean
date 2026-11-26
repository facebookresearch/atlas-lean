/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Regular and quasi-regular symmetric forms

Two topological conditions on a symmetric form `E` on `L²(X; m)` under which a Markov process
can be associated with it.

* **Regularity** (M. Fukushima): `D[E] ∩ C_c(X)` is dense in `D[E]` for `E₁` and dense in
  `C_c(X)` for the uniform norm (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric
  Markov Processes*, 2nd revised and extended ed., de Gruyter, 2011, §1.1; M. Röckner and
  B. Schmuland, *Quasi-regular Dirichlet forms: examples and counterexamples*, Canad. J. Math.
  47 (1995), 165–200, condition (0.1)). It presupposes a locally compact separable metric space
  and a Radon measure of full support; those are hypotheses of the theorems that use it.
* **Quasi-regularity** (S. Albeverio and Z.-M. Ma, 1991; Z.-M. Ma and M. Röckner, 1992):
  conditions (QR1)–(QR3) of Röckner–Schmuland, Definition 0.7, phrased with `E`-nests,
  `E`-exceptional sets and `E`-quasi-continuity (their Definition 0.5), on an arbitrary
  Hausdorff space.

Here everything is for *symmetric* forms (the framework of `SymmetricForm`). Röckner and
Schmuland state Definitions 0.5 and 0.7 for semi-Dirichlet forms and note (Remark 0.8(iv)) that
nests, quasi-continuity and quasi-regularity depend on the form only through its symmetric part.

## Main definitions

* `SymmetricForm.IsRegular`.
* `SymmetricForm.vanishingOutside`, `SymmetricForm.IsNest`, `SymmetricForm.IsExceptional`,
  `SymmetricForm.IsQuasiContinuous`, `SymmetricForm.IsQuasiRegular`.

## Main results

* `SymmetricForm.isNest_const_univ`: the constant sequence `X, X, …` is a nest, so the empty set
  is exceptional and continuous functions are quasi-continuous.

The theorems that give these notions their meaning, Fukushima's construction of a Hunt process
from a regular Dirichlet form and the Albeverio–Ma–Röckner characterisation of quasi-regular
Dirichlet forms by right processes, are not stated: Mathlib has no Hunt or right processes, as
`MathlibExt/Probability/DirichletForm/Resolvent.lean` explains. The proof that regular forms are
quasi-regular is in `MathlibExt/Probability/DirichletForm/RegularToQuasiRegular.lean`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped CompactlySupported

namespace MathlibExt.Probability.DirichletForm

namespace SymmetricForm

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
variable (E : SymmetricForm m)

/-- **Regular symmetric form.** `D[E] ∩ C_c(X)` is `E₁`-dense in `D[E]` and uniformly dense in
`C_c(X)`: every `u ∈ D[E]` is an `E₁`-limit of elements of `D[E]` with a continuous compactly
supported version, and every `g ∈ C_c(X)` is a uniform limit of such versions (Fukushima, Oshima
and Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, §1.1; M. Röckner
and B. Schmuland, *Canad. J. Math.* 47 (1995), condition (0.1)). -/
def IsRegular : Prop :=
  (∀ u ∈ E.domain, ∀ ε > 0, ∃ v ∈ E.domain, (∃ f : X →C_c ℝ, (v : X → ℝ) =ᵐ[m] f) ∧
    E.energyOne (u - v) (u - v) < ε) ∧
  (∀ g : X →C_c ℝ, ∀ ε > 0, ∃ f : X →C_c ℝ, (∃ v ∈ E.domain, (v : X → ℝ) =ᵐ[m] f) ∧
    ∀ x, |f x - g x| < ε)

/-- **Elements of the domain vanishing outside a set.** `D[E]_F = {u ∈ D[E] : u = 0 m-a.e. on
X \ F}` (M. Röckner and B. Schmuland, *Canad. J. Math.* 47 (1995), Definition 0.5(i), equation
(0.3)). -/
def vanishingOutside (F : Set X) : Set (Lp ℝ 2 m) :=
  {u | u ∈ E.domain ∧ ∀ᵐ x ∂m, x ∈ Fᶜ → u x = 0}

/-- **`E`-nest.** An increasing sequence of closed sets `F₀ ⊆ F₁ ⊆ ⋯` such that
`⋃ₖ D[E]_{Fₖ}` is `E₁`-dense in `D[E]` (M. Röckner and B. Schmuland, *Canad. J. Math.* 47
(1995), Definition 0.5(ii)). -/
def IsNest (F : ℕ → Set X) : Prop :=
  Monotone F ∧ (∀ k, _root_.IsClosed (F k)) ∧
    ∀ u ∈ E.domain, ∀ ε > 0, ∃ k, ∃ v ∈ E.vanishingOutside (F k), E.energyOne (u - v) (u - v) < ε

/-- **`E`-exceptional set.** `N ⊆ ⋂ₖ (X \ Fₖ)` for some `E`-nest `(Fₖ)` (M. Röckner and
B. Schmuland, *Canad. J. Math.* 47 (1995), Definition 0.5(iii)). A property holds
`E`-quasi-everywhere if it holds outside an `E`-exceptional set. -/
def IsExceptional (N : Set X) : Prop :=
  ∃ F, E.IsNest F ∧ N ⊆ ⋂ k, (F k)ᶜ

/-- **`E`-quasi-continuous function.** There is an `E`-nest `(Fₖ)` such that the restriction of
`f` to each `Fₖ` is continuous (M. Röckner and B. Schmuland, *Canad. J. Math.* 47 (1995),
Definition 0.5(iv); a function defined only quasi-everywhere is represented by any extension, its
values off `⋃ₖ Fₖ` playing no role). -/
def IsQuasiContinuous (f : X → ℝ) : Prop :=
  ∃ F, E.IsNest F ∧ ∀ k, ContinuousOn f (F k)

/-- **Quasi-regular symmetric form.** (QR1) there is an `E`-nest of compact sets; (QR2) there is
an `E₁`-dense subset of `D[E]` whose elements have `E`-quasi-continuous `m`-versions; (QR3)
there are `uₙ ∈ D[E]` with `E`-quasi-continuous `m`-versions `ũₙ` and an `E`-exceptional set `N`
such that `{ũₙ}` separates the points of `X \ N` (S. Albeverio and Z.-M. Ma, 1991;
Z.-M. Ma and M. Röckner, 1992; as stated in M. Röckner and B. Schmuland, *Canad. J. Math.* 47
(1995), Definition 0.7, here for symmetric forms). -/
def IsQuasiRegular : Prop :=
  (∃ F, E.IsNest F ∧ ∀ k, IsCompact (F k)) ∧
  (∃ D₀ ⊆ (E.domain : Set (Lp ℝ 2 m)),
    (∀ u ∈ E.domain, ∀ ε > 0, ∃ v ∈ D₀, E.energyOne (u - v) (u - v) < ε) ∧
    ∀ v ∈ D₀, ∃ f : X → ℝ, E.IsQuasiContinuous f ∧ (v : X → ℝ) =ᵐ[m] f) ∧
  (∃ (u : ℕ → Lp ℝ 2 m) (f : ℕ → X → ℝ) (N : Set X),
    (∀ n, u n ∈ E.domain ∧ E.IsQuasiContinuous (f n) ∧ (u n : X → ℝ) =ᵐ[m] f n) ∧
    E.IsExceptional N ∧ ∀ x ∈ Nᶜ, ∀ y ∈ Nᶜ, x ≠ y → ∃ n, f n x ≠ f n y)

/-- **The whole space is a nest.** The constant sequence `X, X, …` is an `E`-nest, since
`D[E]_X = D[E]`. -/
theorem isNest_const_univ : E.IsNest fun _ => univ := by
  refine ⟨fun _ _ _ => le_rfl, fun _ => isClosed_univ, fun u hu ε hε => ⟨0, u, ?_, ?_⟩⟩
  · exact ⟨hu, Eventually.of_forall fun x hx => absurd (mem_univ x) hx⟩
  · simp [energyOne, hε]

/-- **The empty set is `E`-exceptional.** -/
theorem isExceptional_empty : E.IsExceptional (∅ : Set X) :=
  ⟨_, E.isNest_const_univ, empty_subset _⟩

/-- **Continuous functions are `E`-quasi-continuous.** -/
theorem isQuasiContinuous_of_continuous {f : X → ℝ} (hf : Continuous f) :
    E.IsQuasiContinuous f :=
  ⟨_, E.isNest_const_univ, fun _ => hf.continuousOn⟩

end SymmetricForm

end MathlibExt.Probability.DirichletForm
