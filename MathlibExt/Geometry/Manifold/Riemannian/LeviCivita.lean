/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Geometry/LeviCivita.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `levi_civita_exists_unique` (manifest
`manifests/problems/levi_civita_exists_unique.toml`, rev 1, submitted by Kim Morrison, status
archived).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"). You may obtain a copy at
https://www.apache.org/licenses/LICENSE-2.0. The adapted portions are distributed on an "AS IS"
basis, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License
for the specific language governing permissions and limitations. lean-eval ships no NOTICE file.

The adapted portions are the definition `SameOnSmooth`, the statement of
`levi_civita_exists_unique` and the module documentation, as recorded in the former wanted module
`WantedExt/Geometry/LeviCivitaWanted.lean`. ATLAS converted the `@[eval_problem]` theorem into a
Batteries `theorem_wanted` and placed the declarations in the namespace below; it then moved the
declarations to this module, supplied the proof, and removed from the module documentation the
paragraph on what mathlib lacked when the problem was written. Mathematical statements are
unchanged.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import MathlibExt.Geometry.MetricCompatibilityShared
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Fundamental theorem of Riemannian geometry (Levi-Civita)

This file proves `levi_civita_exists_unique`: on a Hausdorff `C^∞` Riemannian manifold, possibly
with boundary or corners, there is a smooth torsion-free covariant derivative on the tangent bundle
that is compatible with the metric, and it is unique on smooth vector fields. On the way it proves
`contMDiffCovariantDerivative_leviCivitaConnection`: Mathlib's Levi-Civita connection
`CovariantDerivative.leviCivitaConnection` of a `C^∞` metric is a `C^∞` covariant derivative.

§38 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. On a `C^∞`
finite-dimensional Riemannian manifold `(M, g)`, there exists a unique
smooth torsion-free covariant derivative on `TM` that is compatible with
the metric — the **Levi-Civita connection**.

A `[T2Space M]` hypothesis was added on 2026-06-14. We are not certain the
statement is wrong without it, but it looks suspicious: uniqueness on
smooth sections reduces to global smooth vector fields spanning every
tangent space, which (given how mathlib's bump-function machinery works)
needs `M` Hausdorff, and mathlib does not bundle Hausdorffness into
`IsManifold`. Since the classical Levi-Civita theorem is always stated for
(Hausdorff) manifolds, the original intent is better reflected with
`[T2Space M]`, so we add it now. Lorenzo Luccioli, using Harmonic's
Aristotle, flagged the missing hypothesis. Thanks to both.

## Proof

The pinned Mathlib constructs `CovariantDerivative.leviCivitaConnection` from the Koszul formula
and proves that it is torsion-free and metric-compatible, and that such a connection is unique on
differentiable vector fields; it does not yet prove that the connection is smooth. The predicate
`IsMetricCompatible` lives in `MathlibExt.Geometry.MetricCompatibilityShared`, which also shows
that Mathlib's notion of metric compatibility implies it
(`IsMetricCompatible.of_isMetricCompatible`).

* Smoothness. Fix `x₀` and the trivialization of the tangent bundle at `x₀`, with its local
  frame `s_b` (`b` in the model space). For a smooth vector field `Y`, the Koszul formula
  expresses `⟪∇_{s_b} Y, s_c⟫` near `x₀` through derivatives of inner products of smooth vector
  fields and Lie brackets, so it is smooth at `x₀`. A vector field is smooth at `x₀` as soon as
  its inner products with every `s_c` are: in coordinates it is obtained from them by applying
  the inverse of the Gram operator `a ↦ ⟪s_a, s_·⟫` of the metric, which is smooth at `x₀`.
  Hence each `∇_{s_b} Y` is smooth at `x₀`, and so is `∇ Y` as a section of the endomorphism
  bundle.
* Uniqueness. `IsMetricCompatible` only involves globally smooth vector fields. Every tangent
  vector of a Hausdorff manifold is the value of a globally smooth vector field (a smooth bump
  function times a local extension), which is where `[T2Space M]` is used. With such fields the
  Koszul formula holds for any torsion-free connection satisfying `IsMetricCompatible`, and it
  determines `⟪∇_v Y, w⟫` for all tangent vectors `v` and `w`.
-/

@[expose] public section

open MathlibExt.Geometry.MetricCompatibilityShared

namespace MathlibExt.Geometry.LeviCivitaWanted
namespace Geometry
namespace LeviCivita

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

set_option linter.dupNamespace false in
/-- **Agreement of covariant derivatives on smooth vector fields.** Let $M$ be a smooth manifold,
possibly with boundary or corners, modelled on a finite-dimensional real normed space, whose
tangent bundle carries a smooth Riemannian metric. Two covariant derivatives $\nabla$ and
$\nabla'$ on the tangent bundle of $M$ agree on smooth sections when $\nabla_v Y = \nabla'_v Y$
for every smooth vector field $Y$ on $M$, every point $x \in M$ and every tangent vector $v$ at
$x$.

Covariant derivatives here act on all sections of the tangent bundle, not only smooth ones, so the
uniqueness in the Levi-Civita theorem is stated as agreement on smooth vector fields. -/
def SameOnSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov cov' : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (Y : Π x : M, TangentSpace I x), CMDiff ∞ (T% Y) →
    ∀ (x : M) (v : TangentSpace I x), cov Y x v = cov' Y x v

section Coordinates

/-! ### Smoothness criteria in the trivialization at a point -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A family of continuous linear maps out of a finite-dimensional space is smooth at a point as
soon as all its evaluations are. -/
private theorem contMDiffAt_clm_of_apply {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : M → F →L[ℝ] G} {x₀ : M} {n : ℕ∞ω}
    (h : ∀ v, CMDiffAt n (fun x ↦ f x v) x₀) : CMDiffAt n f x₀ := by
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt,
    contDiffWithinAt_clm_apply]
  intro v
  have hv := h v
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
  exact hv

variable [IsManifold I ∞ M]

/-- The local frame of the tangent bundle given by the trivialization at `x₀`: its value at `y`
is the tangent vector with coordinates `b` in that trivialization. -/
private noncomputable def frame (x₀ : M) (b : E) : Π y : M, TangentSpace I y :=
  fun y ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ y b

private theorem contMDiffAt_frame {x₀ y : M} (b : E)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    CMDiffAt ∞ (T% (frame (I := I) x₀ b)) y := by
  rw [(trivializationAt E (TangentSpace I) x₀).contMDiffAt_section_iff hy]
  apply (contMDiffAt_const (c := b)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hy] with z hz
  simp [frame, Trivialization.symmL_apply _ hz, Trivialization.apply_mk_symm _ hz]

/-- The derivative of a smooth function along a smooth vector field is smooth. -/
private theorem contMDiffAt_mvfderiv_apply {f : M → ℝ} {X : Π x : M, TangentSpace I x}
    {x₀ : M} (hf : CMDiffAt ∞ f x₀) (hX : CMDiffAt ∞ (T% X) x₀) :
    CMDiffAt ∞ (fun x ↦ mvfderiv I f x (X x)) x₀ :=
  (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).contMDiffAt.comp x₀
    ((hf.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hX hf)

variable [FiniteDimensional ℝ E]

/-- A section of the endomorphism bundle of the tangent bundle is smooth at `x₀` as soon as its
values on the local frame at `x₀` are smooth vector fields there. -/
private theorem contMDiffAt_endomorphism_of_frame
    {A : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x} {x₀ : M}
    (h : ∀ b : E, CMDiffAt ∞ (T% (fun x ↦ A x (frame (I := I) x₀ b x))) x₀) :
    CMDiffAt ∞ (fun x ↦ (⟨x, A x⟩ :
      TotalSpace (E →L[ℝ] E) fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)) x₀ := by
  set e := trivializationAt E (TangentSpace I) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, contMDiffAt_clm_of_apply fun b ↦ ?_⟩
  have hb := h b
  rw [contMDiffAt_section_iff] at hb
  refine hb.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply, frame]
  exact Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hx _

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] in
/-- The inner product of two smooth vector fields is smooth (`ContMDiffAt.inner_bundle`, stated
for vector fields so that unification finds the bundle). -/
private theorem contMDiffAt_inner_vectorField {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    CMDiffAt ∞ (fun y ↦ inner ℝ (X y) (Y y)) x :=
  ContMDiffAt.inner_bundle hX hY

/-- The Gram operator of the metric in the trivialization at `x₀`: at `x`, it sends `a` to the
linear form `c ↦ ⟪s_a(x), s_c(x)⟫`, where `s` is `frame x₀`. -/
private noncomputable def gram (x₀ x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ (E := TangentSpace I x)).bilinearComp
    ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x)
    ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x)

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] in
private theorem gram_apply (x₀ x : M) (a c : E) :
    gram (I := I) x₀ x a c = inner ℝ (frame (I := I) x₀ a x) (frame (I := I) x₀ c x) :=
  rfl

private theorem contMDiffAt_gram (x₀ : M) : CMDiffAt ∞ (gram (I := I) x₀) x₀ := by
  have hx₀ := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) x₀
  refine contMDiffAt_clm_of_apply fun a ↦ contMDiffAt_clm_of_apply fun c ↦ ?_
  simp only [gram_apply]
  exact contMDiffAt_inner_vectorField (contMDiffAt_frame a hx₀) (contMDiffAt_frame c hx₀)

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] in
private theorem injective_gram {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Function.Injective (gram (I := I) x₀ x) := by
  intro a a' h
  have h0 : gram (I := I) x₀ x (a - a') = 0 := by rw [map_sub, h, sub_self]
  have h1 : gram (I := I) x₀ x (a - a') (a - a') = 0 := by
    rw [h0]
    rfl
  rw [gram_apply, real_inner_self_eq_norm_sq] at h1
  have h2 : frame (I := I) x₀ (a - a') x = 0 := by simpa using h1
  have h3 := congrArg
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x) h2
  rw [frame, Trivialization.continuousLinearMapAt_symmL _ hx, map_zero] at h3
  exact sub_eq_zero.mp h3

omit [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] in
private theorem isInvertible_gram {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (gram (I := I) x₀ x).IsInvertible := by
  have hrank : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]
  refine ⟨(LinearMap.linearEquivOfInjective (gram (I := I) x₀ x).toLinearMap
    (injective_gram hx) hrank).toContinuousLinearEquiv, ?_⟩
  ext a
  rfl

/-- A vector field is smooth at `x₀` as soon as its inner products with the local frame at `x₀`
are smooth there. -/
private theorem contMDiffAt_of_inner_frame {σ : Π x : M, TangentSpace I x} {x₀ : M}
    (h : ∀ c : E, CMDiffAt ∞ (fun x ↦ inner ℝ (σ x) (frame (I := I) x₀ c x)) x₀) :
    CMDiffAt ∞ (T% σ) x₀ := by
  set e := trivializationAt E (TangentSpace I) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  rw [contMDiffAt_section_iff]
  have hℓ : CMDiffAt ∞ (fun x ↦ gram (I := I) x₀ x (e ⟨x, σ x⟩).2) x₀ := by
    refine contMDiffAt_clm_of_apply fun c ↦ (h c).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
    rw [gram_apply, frame, e.symmL_apply hx, e.symm_apply_apply_mk hx]
  have hinv : CMDiffAt ∞ (fun x ↦ ContinuousLinearMap.inverse (gram (I := I) x₀ x)) x₀ :=
    (isInvertible_gram hx₀).contDiffAt_map_inverse.comp_contMDiffAt (contMDiffAt_gram x₀)
  refine (hinv.clm_apply hℓ).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
  exact ((isInvertible_gram hx).inverse_apply_self _).symm

/-- The right-hand side of the Koszul formula is smooth at a point where the three vector fields
are smooth. -/
private theorem contMDiffAt_koszul {X Y Z : Π x : M, TangentSpace I x} {x₀ : M}
    (hX : CMDiffAt ∞ (T% X) x₀) (hY : CMDiffAt ∞ (T% Y) x₀) (hZ : CMDiffAt ∞ (T% Z) x₀) :
    CMDiffAt ∞ (fun x ↦ (mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x)
      + mvfderiv I (fun y ↦ inner ℝ (Z y) (X y)) x (Y x)
      - mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x)
      - inner ℝ (Y x) (mlieBracket I X Z x)
      - inner ℝ (Z x) (mlieBracket I Y X x)
      + inner ℝ (X x) (mlieBracket I Z Y x)) / 2) x₀ := by
  have hmn : minSmoothness ℝ ((⊤ : ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]; simp
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have : IsManifold I (∞ + 1) M := by
    rw [show (∞ : ℕ∞ω) + 1 = ∞ from rfl]; infer_instance
  have hXZ : CMDiffAt ∞ (T% (mlieBracket I X Z)) x₀ :=
    ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) hX hZ hmn
  have hYX : CMDiffAt ∞ (T% (mlieBracket I Y X)) x₀ :=
    ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) hY hX hmn
  have hZY : CMDiffAt ∞ (T% (mlieBracket I Z Y)) x₀ :=
    ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) hZ hY hmn
  have h1 := contMDiffAt_mvfderiv_apply (contMDiffAt_inner_vectorField hY hZ) hX
  have h2 := contMDiffAt_mvfderiv_apply (contMDiffAt_inner_vectorField hZ hX) hY
  have h3 := contMDiffAt_mvfderiv_apply (contMDiffAt_inner_vectorField hX hY) hZ
  have h4 := contMDiffAt_inner_vectorField hY hXZ
  have h5 := contMDiffAt_inner_vectorField hZ hYX
  have h6 := contMDiffAt_inner_vectorField hX hZY
  exact (((((h1.add h2).sub h3).sub h4).sub h5).add h6).div_const 2

private theorem contMDiffAt_leviCivitaConnection {Y : Π x : M, TangentSpace I x}
    (hY : CMDiff ∞ (T% Y)) (x₀ : M) :
    CMDiffAt ∞ (fun x ↦ (⟨x, leviCivitaConnection I M Y x⟩ :
      TotalSpace (E →L[ℝ] E) fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)) x₀ := by
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  refine contMDiffAt_endomorphism_of_frame fun b ↦ contMDiffAt_of_inner_frame fun c ↦ ?_
  refine (contMDiffAt_koszul (contMDiffAt_frame b hx₀) (hY x₀)
    (contMDiffAt_frame c hx₀)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀] with x hx
  exact leviCivitaConnection_apply_inner I
    ((contMDiffAt_frame b hx).mdifferentiableAt (by simp))
    ((hY x).mdifferentiableAt (by simp)) ((contMDiffAt_frame c hx).mdifferentiableAt (by simp))

end Coordinates

set_option linter.dupNamespace false in
/-- **Smoothness of the Levi-Civita connection.** Let $M$ be a smooth manifold, possibly with
boundary or corners, modelled on a finite-dimensional real normed space, whose tangent bundle
carries a smooth Riemannian metric. Then Mathlib's Levi-Civita connection
`CovariantDerivative.leviCivitaConnection` of $M$ is a smooth covariant derivative: for every
smooth vector field $Y$ on $M$, the section $x \mapsto \nabla Y(x)$ of the bundle of
endomorphisms of the tangent bundle is smooth.

Source: the Koszul formula (O. Knill, Some Fundamental Theorems in Mathematics,
arXiv:1807.08416, §38), read in the local frame of a chart, where it expresses the coefficients
of the connection through the metric coefficients, their first derivatives and the inverse of
the Gram matrix of the metric. -/
theorem contMDiffCovariantDerivative_leviCivitaConnection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) ∞ where
  contMDiff := ⟨fun {_} hσ x _ ↦
    (contMDiffAt_leviCivitaConnection (contMDiffOn_univ.mp hσ) x).contMDiffWithinAt⟩

section Uniqueness

/-! ### Uniqueness on smooth vector fields -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- On a Hausdorff manifold, every tangent vector is the value of a globally smooth vector
field: a smooth bump function times the local extension `FiberBundle.extend`. -/
private theorem exists_contMDiff_vectorField_eq [T2Space M] (x : M) (w : TangentSpace I x) :
    ∃ Z : Π y : M, TangentSpace I y, CMDiff ∞ (T% Z) ∧ Z x = w := by
  obtain ⟨ψ⟩ : Nonempty (SmoothBumpFunction I x) := inferInstance
  set e := trivializationAt E (TangentSpace I) x
  refine ⟨(ψ : M → ℝ) • FiberBundle.extend E w, ?_, by simp⟩
  refine ContMDiffOn.smul_section_of_tsupport (u := e.baseSet) ψ.contMDiff.contMDiffOn
    e.open_baseSet (by simpa [e] using ψ.tsupport_subset_chartAt_source) fun y hy ↦ ?_
  refine ContMDiffAt.contMDiffWithinAt ?_
  rw [e.contMDiffAt_section_iff hy]
  refine (contMDiffAt_const (c := (e ⟨x, w⟩).2)).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
  simp [e, FiberBundle.extend, Trivialization.apply_mk_symm _ hz]

variable [CompleteSpace E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- The Koszul formula for a torsion-free covariant derivative satisfying `IsMetricCompatible`,
for globally smooth vector fields. -/
private theorem inner_eq_koszul (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    inner ℝ (cov Y x (X x)) (Z x) =
      (mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ inner ℝ (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x)
        - inner ℝ (Y x) (mlieBracket I X Z x)
        - inner ℝ (Z x) (mlieBracket I Y X x)
        + inner ℝ (X x) (mlieBracket I Z Y x)) / 2 := by
  have hXd : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hYd : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZd : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have eq1a := hmet Y Z hY hZ x (X x)
  have eq2a := hmet Z X hZ hX x (Y x)
  have eq3a := hmet X Y hX hY x (Z x)
  rw [cov.torsion_eq_zero_iff] at htor
  have eq1b := congrArg (inner ℝ (Y x)) (htor hXd hZd)
  have eq2b := congrArg (inner ℝ (Z x)) (htor hYd hXd)
  have eq3b := congrArg (inner ℝ (X x)) (htor hZd hYd)
  simp only [inner_sub_right] at eq1b eq2b eq3b
  rw [real_inner_comm (cov X x (Z x)) (Y x)] at eq1b
  rw [real_inner_comm (cov Y x (X x)) (Z x)] at eq2b
  rw [real_inner_comm (cov Z x (Y x)) (X x)] at eq3b
  linear_combination (-eq1a - eq2a + eq3a - eq1b - eq2b + eq3b) / 2

/-- Mathlib's Levi-Civita connection satisfies `IsMetricCompatible`. -/
private theorem isMetricCompatible_leviCivitaConnection' :
    IsMetricCompatible (leviCivitaConnection I M) :=
  .of_isMetricCompatible (isMetricCompatible_leviCivitaConnection I)

end Uniqueness

set_option linter.dupNamespace false in
/-- **Fundamental theorem of Riemannian geometry (Levi-Civita).** Let $M$ be a Hausdorff smooth
manifold, possibly with boundary or corners, modelled on a finite-dimensional real normed space,
whose tangent bundle carries a smooth Riemannian metric. Then there is a smooth covariant
derivative $\nabla$ on the tangent bundle of $M$ that is torsion-free and compatible with the
metric, and every smooth, torsion-free, metric-compatible covariant derivative $\nabla'$ on the
tangent bundle of $M$ agrees with $\nabla$ on smooth vector fields: $\nabla'_v Y = \nabla_v Y$ for
every smooth vector field $Y$ on $M$, every point $x \in M$ and every tangent vector $v$ at $x$.

Source: T. Levi-Civita, Nozione di parallelismo in una varietà qualunque, Rend. Circ. Mat. Palermo
42 (1917). Listed as §38 in O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `levi_civita_exists_unique`. -/
theorem levi_civita_exists_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] :
    ∃ cov : CovariantDerivative I E (TangentSpace I (M := M)),
      (ContMDiffCovariantDerivative cov ∞ ∧
        cov.torsion = 0 ∧ IsMetricCompatible cov) ∧
      ∀ cov' : CovariantDerivative I E (TangentSpace I (M := M)),
        (ContMDiffCovariantDerivative cov' ∞ ∧
          cov'.torsion = 0 ∧ IsMetricCompatible cov') →
        SameOnSmooth cov cov' := by
  refine ⟨leviCivitaConnection I M, ⟨contMDiffCovariantDerivative_leviCivitaConnection,
    torsion_leviCivitaConnection_eq_zero I, isMetricCompatible_leviCivitaConnection'⟩, ?_⟩
  rintro cov' ⟨-, htor', hmet'⟩ Y hY x v
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_vectorField_eq x v
  refine ext_inner_right ℝ fun w ↦ ?_
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_vectorField_eq x w
  rw [inner_eq_koszul _ (torsion_leviCivitaConnection_eq_zero I)
      isMetricCompatible_leviCivitaConnection' hX hY hZ,
    inner_eq_koszul _ htor' hmet' hX hY hZ]

end LeviCivita
end Geometry

end MathlibExt.Geometry.LeviCivitaWanted
