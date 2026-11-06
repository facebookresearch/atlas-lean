/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.MetricSpace.HausdorffDistance

import MathlibExt.Analysis.Normed.Module.DualDistanceFormula

@[expose] public section

/-!
# Topological annihilators and the bipolar theorem

For a subspace `S` of a normed space `E` over `𝕜 = ℝ, ℂ`, the
**topological annihilator** `S.topologicalAnnihilator` is the subspace of
the continuous dual `E →L[𝕜] 𝕜` consisting of the functionals that vanish
on `S`, and the **topological coannihilator** of a subspace `Φ` of the
dual is the subspace of `E` killed by every functional in `Φ`. The main
result is the **bipolar theorem**
(`topologicalAnnihilator_topologicalCoannihilator_eq_topologicalClosure`):
the double annihilator of `S` is the topological closure of `S`.

This is the topological counterpart of Mathlib's algebraic dual
annihilator (`Submodule.dualAnnihilator`, which uses the algebraic dual
`Module.Dual` and gives back the subspace itself, with no closure).
The new content here is the use of continuity: a functional that vanishes
on `S` vanishes on its closure, and conversely a point outside the closure
is separated from `S` by a functional in the annihilator. The separation
step reuses the existing dual distance formula: its attaining functional
vanishes on `S` and takes the positive value `infDist x S` at `x`.

This is a companion to the Hahn-Banach material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean`
(March 2, 2021 lecture) and to the dual distance formula of batch 51,
which proves a norm/infimum statement for a single functional
(`exists_annihilating_apply_eq_infDist`) rather than the annihilator
submodules and the bipolar identity proved here. It is not one of the
72 v1 targets, and it is not in the pinned Mathlib or in base MathlibExt:
Mathlib has only the algebraic dual annihilator and the polar sets of
locally convex spaces, neither of which gives the double annihilator
as a topological closure. No completeness hypothesis is used.

## Main declarations

* `Submodule.topologicalAnnihilator` : the annihilator of `S` in the
  continuous dual.
* `Submodule.topologicalCoannihilator` : the coannihilator of `Φ` in `E`.
* `Submodule.exists_mem_topologicalAnnihilator_apply_ne_zero` :
  separation of a point outside the closure by an annihilating functional.
* `Submodule.exists_mem_topologicalAnnihilator_apply_eq_one` : the
  normalized form, with value `1` at the separated point.
* `Submodule.topologicalAnnihilator_topologicalCoannihilator_eq_topologicalClosure` :
  the bipolar theorem.
* `Submodule.topologicalAnnihilator_eq_bot_iff_dense` : the annihilator
  vanishes exactly for dense subspaces.
* `Submodule.topologicalAnnihilator_eq_iff_topologicalClosure_eq` :
  the annihilator determines the closure.
-/

namespace Submodule

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Topological annihilator.** Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, with continuous dual $E^*$. The topological annihilator of a subspace $S$ of $E$
is the subspace of $E^*$ consisting of the continuous linear functionals $f$ with $f(x) = 0$
for all $x \in S$. -/
def topologicalAnnihilator (S : Submodule 𝕜 E) : Submodule 𝕜 (E →L[𝕜] 𝕜) where
  carrier := { f | ∀ x ∈ S, f x = 0 }
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hf hg x hx => by simp [hf x hx, hg x hx]
  smul_mem' := fun c f hf x hx => by simp [hf x hx]

/-- **Topological coannihilator.** Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, with continuous dual $E^*$. The topological coannihilator of a subspace $\Phi$ of
$E^*$ is the subspace of $E$ consisting of the vectors $x$ with $f(x) = 0$ for all
$f \in \Phi$. -/
def topologicalCoannihilator (Φ : Submodule 𝕜 (E →L[𝕜] 𝕜)) : Submodule 𝕜 E where
  carrier := { x | ∀ f ∈ Φ, f x = 0 }
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hx hy f hf => by simp [hx f hf, hy f hf]
  smul_mem' := fun c x hx f hf => by simp [hx f hf]

/-- **Membership in the topological annihilator.** Let $E$ be a normed space over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let $S$ be a subspace of $E$, and let
$f : E \to \mathbb{K}$ be a continuous linear functional. Then $f$ lies in the topological
annihilator of $S$ if and only if $f(x) = 0$ for every $x \in S$. -/
theorem mem_topologicalAnnihilator {S : Submodule 𝕜 E} {f : E →L[𝕜] 𝕜} :
    f ∈ S.topologicalAnnihilator ↔ ∀ x ∈ S, f x = 0 := Iff.rfl

/-- **Membership in the topological coannihilator.** Let $E$ be a normed space over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let $\Phi$ be a subspace of the continuous dual
of $E$, and let $x \in E$. Then $x$ lies in the topological coannihilator of $\Phi$ if and only if
$f(x) = 0$ for every $f \in \Phi$. -/
theorem mem_topologicalCoannihilator {Φ : Submodule 𝕜 (E →L[𝕜] 𝕜)} {x : E} :
    x ∈ Φ.topologicalCoannihilator ↔ ∀ f ∈ Φ, f x = 0 := Iff.rfl

/-- **The topological annihilator reverses inclusion.** Let $E$ be a normed space over
$\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let $S \subseteq T$ be
subspaces of $E$. Then the topological annihilator of $T$ is contained in the topological
annihilator of $S$. -/
theorem topologicalAnnihilator_anti {S T : Submodule 𝕜 E} (h : S ≤ T) :
    T.topologicalAnnihilator ≤ S.topologicalAnnihilator := by
  intro f hf x hx
  exact (mem_topologicalAnnihilator.mp hf) x (h hx)

/-- **The topological coannihilator is antitone.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with continuous dual $E^*$. If $\Phi \subseteq \Psi$
are subspaces of $E^*$, then the topological coannihilator of $\Psi$ is contained in the
topological coannihilator of $\Phi$. -/
theorem topologicalCoannihilator_anti {Φ Ψ : Submodule 𝕜 (E →L[𝕜] 𝕜)} (h : Φ ≤ Ψ) :
    Ψ.topologicalCoannihilator ≤ Φ.topologicalCoannihilator := by
  intro x hx f hf
  exact (mem_topologicalCoannihilator.mp hx) f (h hf)

/-- **Topological annihilator of the zero subspace.** Let $E$ be a normed space over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. The topological annihilator of the zero subspace
of $E$ is the whole continuous dual of $E$. -/
@[simp]
theorem topologicalAnnihilator_bot :
    (⊥ : Submodule 𝕜 E).topologicalAnnihilator = ⊤ := by
  ext f
  constructor
  · intro _
    trivial
  · intro _ x hx
    rw [(Submodule.mem_bot 𝕜).mp hx]
    simp

/-- **Topological annihilator of the whole space.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with continuous dual $E^*$. The topological
annihilator of $E$, viewed as a subspace of itself, is the zero subspace of $E^*$: a continuous
linear functional vanishing everywhere on $E$ is zero. -/
@[simp]
theorem topologicalAnnihilator_top :
    (⊤ : Submodule 𝕜 E).topologicalAnnihilator = ⊥ := by
  ext f
  simp only [mem_topologicalAnnihilator, Submodule.mem_top, true_implies,
    Submodule.mem_bot]
  constructor
  · intro h
    ext x
    exact h x
  · intro h x
    rw [h]
    simp

/-- **Topological coannihilator of the zero subspace.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with continuous dual $E^*$. The topological
coannihilator of the zero subspace of $E^*$ is all of $E$. -/
@[simp]
theorem topologicalCoannihilator_bot :
    (⊥ : Submodule 𝕜 (E →L[𝕜] 𝕜)).topologicalCoannihilator = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _ f hf
    rw [(Submodule.mem_bot 𝕜).mp hf]
    simp

/-- **Topological coannihilator of the whole dual.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with continuous dual $E^*$. The topological
coannihilator of $E^*$ itself is the zero subspace of $E$: a vector killed by every continuous
linear functional is zero.

The proof uses the Hahn–Banach norming functional. -/
theorem topologicalCoannihilator_top :
    (⊤ : Submodule 𝕜 (E →L[𝕜] 𝕜)).topologicalCoannihilator = ⊥ := by
  ext x
  simp only [mem_topologicalCoannihilator, Submodule.mem_top, true_implies,
    Submodule.mem_bot]
  constructor
  · intro h
    by_contra hx
    obtain ⟨g, -, hg_val⟩ := exists_dual_vector'' 𝕜 x
    have hgx : g x ≠ 0 := by
      rw [hg_val]
      exact RCLike.ofReal_ne_zero.mpr (norm_pos_iff.mpr hx).ne'
    exact hgx (h g)
  · intro h
    rw [h]
    simp

/-- **A subspace lies in its double annihilator.** Let $E$ be a normed space over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. Every subspace $S$ of $E$ is contained in the
topological coannihilator of the topological annihilator of $S$. -/
theorem le_topologicalCoannihilator_topologicalAnnihilator (S : Submodule 𝕜 E) :
    S ≤ S.topologicalAnnihilator.topologicalCoannihilator := by
  intro x hx
  rw [mem_topologicalCoannihilator]
  intro f hf
  exact (mem_topologicalAnnihilator.mp hf) x hx

/-- **Topological annihilator of the closure.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. For every subspace $S$ of $E$, the topological
annihilator of the topological closure $\overline{S}$ equals the topological annihilator of
$S$: a continuous linear functional vanishing on $S$ vanishes on $\overline{S}$. -/
theorem topologicalAnnihilator_topologicalClosure (S : Submodule 𝕜 E) :
    S.topologicalClosure.topologicalAnnihilator = S.topologicalAnnihilator := by
  apply le_antisymm
  · exact topologicalAnnihilator_anti S.le_topologicalClosure
  · intro f hf
    rw [mem_topologicalAnnihilator] at hf ⊢
    intro x hx
    have hS : S ≤ LinearMap.ker (f : E →ₗ[𝕜] 𝕜) := by
      intro y hy
      exact LinearMap.mem_ker.mpr (hf y hy)
    have hfclosed : IsClosed (LinearMap.ker (f : E →ₗ[𝕜] 𝕜) : Set E) :=
      isClosed_singleton.preimage f.continuous
    exact LinearMap.mem_ker.mp (S.topologicalClosure_minimal hS hfclosed hx)

/-- **Separation.** Let $E$ be a normed space over $\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$
or $\mathbb{C}$, let $S$ be a subspace of $E$, and let $x \in E$ lie outside the topological
closure of $S$. Then some continuous linear functional $f$ in the topological annihilator of $S$
satisfies $f(x) \neq 0$. -/
theorem exists_mem_topologicalAnnihilator_apply_ne_zero {S : Submodule 𝕜 E} {x : E}
    (hx : x ∉ S.topologicalClosure) :
    ∃ f ∈ S.topologicalAnnihilator, f x ≠ 0 := by
  have hdist : 0 < Metric.infDist x (S : Set E) :=
    (Metric.infDist_pos_iff_notMem_closure ⟨0, zero_mem S⟩).mp hx
  obtain ⟨f, hfvan, -, hfval⟩ :=
    MathlibExt.Analysis.Normed.Module.DualDistanceFormula.exists_annihilating_apply_eq_infDist
      S x
  refine ⟨f, mem_topologicalAnnihilator.mpr hfvan, ?_⟩
  rw [hfval]
  exact RCLike.ofReal_ne_zero.mpr hdist.ne'

/-- **Separation, normalized.** Let $E$ be a normed space over $\mathbb{K}$, where $\mathbb{K}$ is
$\mathbb{R}$ or $\mathbb{C}$, let $S$ be a subspace of $E$, and let $x \in E$ lie outside the
topological closure of $S$. Then some continuous linear functional $f$ in the topological
annihilator of $S$ satisfies $f(x) = 1$. -/
theorem exists_mem_topologicalAnnihilator_apply_eq_one {S : Submodule 𝕜 E} {x : E}
    (hx : x ∉ S.topologicalClosure) :
    ∃ f ∈ S.topologicalAnnihilator, f x = 1 := by
  obtain ⟨f, hf, hfx⟩ := exists_mem_topologicalAnnihilator_apply_ne_zero hx
  refine ⟨(f x)⁻¹ • f, S.topologicalAnnihilator.smul_mem _ hf, ?_⟩
  rw [smul_apply, smul_eq_mul, inv_mul_cancel₀ hfx]

/-- **Bipolar theorem.** Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$
and let $S$ be a subspace of $E$. The topological coannihilator of the topological annihilator
of $S$, that is, the subspace of vectors of $E$ killed by every continuous linear functional
vanishing on $S$, is the topological closure of $S$. -/
theorem topologicalAnnihilator_topologicalCoannihilator_eq_topologicalClosure
    (S : Submodule 𝕜 E) :
    S.topologicalAnnihilator.topologicalCoannihilator = S.topologicalClosure := by
  apply le_antisymm
  · intro x hx
    by_contra hxnot
    obtain ⟨f, hf, hfx⟩ := exists_mem_topologicalAnnihilator_apply_ne_zero hxnot
    exact hfx (mem_topologicalCoannihilator.mp hx f hf)
  · rw [← topologicalAnnihilator_topologicalClosure S]
    exact le_topologicalCoannihilator_topologicalAnnihilator _

/-- **Density criterion via the annihilator.** Let $E$ be a normed space over $\mathbb{K}$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let $S$ be a subspace of $E$. The topological
annihilator of $S$ is the zero subspace of the continuous dual of $E$ if and only if $S$ is dense
in $E$. -/
theorem topologicalAnnihilator_eq_bot_iff_dense (S : Submodule 𝕜 E) :
    S.topologicalAnnihilator = ⊥ ↔ Dense (S : Set E) := by
  constructor
  · intro h
    have hco : S.topologicalAnnihilator.topologicalCoannihilator = ⊤ := by
      rw [h]
      exact topologicalCoannihilator_bot
    rw [topologicalAnnihilator_topologicalCoannihilator_eq_topologicalClosure] at hco
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hco
  · intro h
    have hcl : S.topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp h
    rw [← topologicalAnnihilator_topologicalClosure S, hcl]
    exact topologicalAnnihilator_top

/-- **The annihilator determines the closure.** Let $E$ be a normed space over $\mathbb{K}$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let $S$ and $T$ be subspaces of $E$. Then $S$ and
$T$ have the same topological annihilator if and only if they have the same topological
closure. -/
theorem topologicalAnnihilator_eq_iff_topologicalClosure_eq {S T : Submodule 𝕜 E} :
    S.topologicalAnnihilator = T.topologicalAnnihilator ↔
      S.topologicalClosure = T.topologicalClosure := by
  constructor
  · intro h
    have hcoa := congrArg (fun Φ => Φ.topologicalCoannihilator) h
    rwa [topologicalAnnihilator_topologicalCoannihilator_eq_topologicalClosure,
      topologicalAnnihilator_topologicalCoannihilator_eq_topologicalClosure] at hcoa
  · intro h
    rw [← topologicalAnnihilator_topologicalClosure S,
      ← topologicalAnnihilator_topologicalClosure T, h]

/-- **Topological annihilator of a sum of subspaces.** Let $E$ be a normed space over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let $S$ and $T$ be subspaces of $E$. The
topological annihilator of $S + T$ is the intersection of the topological annihilators of $S$
and $T$. -/
theorem topologicalAnnihilator_sup (S T : Submodule 𝕜 E) :
    (S ⊔ T).topologicalAnnihilator =
      S.topologicalAnnihilator ⊓ T.topologicalAnnihilator := by
  ext f
  simp only [mem_topologicalAnnihilator, Submodule.mem_sup, Submodule.mem_inf]
  constructor
  · intro h
    refine ⟨fun x hx => h x ⟨x, hx, 0, zero_mem T, by simp⟩,
      fun x hx => h x ⟨0, zero_mem S, x, hx, by simp⟩⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp [map_add, h1 a ha, h2 b hb]

/-- **Topological coannihilator of a sum of subspaces.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with continuous dual $E^*$. For subspaces $\Phi$
and $\Psi$ of $E^*$, the topological coannihilator of their supremum $\Phi + \Psi$ is the
intersection of the topological coannihilators of $\Phi$ and $\Psi$. -/
theorem topologicalCoannihilator_sup (Φ Ψ : Submodule 𝕜 (E →L[𝕜] 𝕜)) :
    (Φ ⊔ Ψ).topologicalCoannihilator =
      Φ.topologicalCoannihilator ⊓ Ψ.topologicalCoannihilator := by
  ext x
  simp only [mem_topologicalCoannihilator, Submodule.mem_sup, Submodule.mem_inf]
  constructor
  · intro h
    refine ⟨fun f hf => h f ⟨f, hf, 0, zero_mem Ψ, by simp⟩,
      fun f hf => h f ⟨0, zero_mem Φ, f, hf, by simp⟩⟩
  · rintro ⟨h1, h2⟩ f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    simp [h1 a ha, h2 b hb]

end Submodule
