/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Topology/NonlinearThreeManifoldGroup.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `nonlinear_three_manifold_group`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/nonlinear_three_manifold_group.toml`, rev 1, submitter Kim Morrison, status
archived): the structure `Closed3Manifold` and the statement of `nonlinear_three_manifold_group`,
with the docstrings and comments they had in the former wanted module
`WantedExt/Topology/NonlinearThreeManifoldGroupWanted.lean`, the citation of Button's paper
corrected as described below.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
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
`MathlibExt.Topology.NonlinearThreeManifoldGroupWanted` namespace. Mathematical statements are
unchanged. Source: J. O. Button, *A 3-manifold group which is not four dimensional linear*,
arXiv:1210.3068 (2012); J. Pure Appl. Algebra 218 (2014), 1604–1619. See the discussion of
[Kir97, Problem 3.33] in the K3 problem list.
Later changes (ATLAS, 2026): the `theorem_wanted` was proved and the declarations moved from
`WantedExt/Topology/NonlinearThreeManifoldGroupWanted.lean` to this `MathlibExt` module with
unchanged names and statements, and the imports of `Batteries.Util.ProofWanted` and of all of
Mathlib were replaced by narrower Mathlib imports. The citation of Button's paper in this notice
and in the docstring of `nonlinear_three_manifold_group` gave it the title *Aspherical 3-manifold
groups not in GL(4, k) for any field k* and the number arXiv:1404.4639, which belongs to an
unrelated paper, and the module documentation gave a shortened form of that title; all three now
name Button's preprint arXiv:1210.3068 under its own title. The docstring of
`nonlinear_three_manifold_group` also says that Button's result holds for every field, and that
the double of the quaternionic space form `S³/Q₈` minus a ball, the witness used in this file,
gives the counterexample over `ℝ` only.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`nonlinear_three_manifold_group`, the private definitions and lemmas it uses, and the parts of
the module documentation that describe the proof.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Quaternion
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Homotopy.Lifting
import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality

/-!
# A 3-manifold group with no faithful representation into GL(4, ℝ) (Button)

`[Kir97, Problem 3.33]`, due to W. Thurston, asks whether every finitely
generated 3-manifold group admits a faithful (injective) representation into
`GL(4, ℝ)`. This is true for hyperbolic 3-manifolds, but Button gave a negative
answer in general: the fundamental groups of certain closed graph manifolds
admit no faithful representation into `GL(4, k)` for *any* field `k` (J. O.
Button, *A 3-manifold group which is not four dimensional linear*, arXiv:1210.3068).

We prove the negative answer to Thurston's question over `ℝ`
(`nonlinear_three_manifold_group`): there is a closed connected 3-manifold whose
fundamental group has no faithful representation into `GL(4, ℝ)`. (Button's
theorem is in fact stronger, ruling out every field.)

A closed connected topological 3-manifold is bundled as `Closed3Manifold`. The
statement is not vacuous: a simply connected witness would have trivial `π₁`,
whose unique map to `GL(4, ℝ)` is injective, contradicting the universal
non-injectivity — so the witness must genuinely have a non-linear fundamental
group.

Mathlib has `FundamentalGroup`, `GL`, `MonoidHom`, and `ChartedSpace`, but no
graph manifolds and none of the linearity obstructions (residual properties,
the structure theory of 3-manifold groups) Button's argument relies on. The
proof below does not need them.

## Proof

The proof does not follow Button: its witness is a reducible 3-manifold, and the
obstruction it uses is special to the field `ℝ`.

* If `a, b` are elements of a group with `a² = b²` and `b a = a⁻¹ b`, and `ρ` is
  an injective homomorphism to `GL(4, ℝ)` with `a² ≠ 1`, then `ρ (a²) = -1`:
  `Z = ρ (a²)` satisfies `Z² = 1`, and the `(-1)`-eigenspace of `Z` is a module
  over the quaternions, hence all of `ℝ⁴`. So every injective
  homomorphism from the quaternion group `Q₈` to `GL(4, ℝ)` sends `-1` to `-1`.
* The witness is the double of the quaternionic space form `S³/Q₈` minus an
  open ball, that is, the connected sum of `S³/Q₈` with its mirror image. It is
  realised as `{(q, t) ∈ (S³/Q₈) × ℝ | t² = f q}`, where in a chart around a
  point `f` is the distance to that point minus a small radius. Its charts
  come from the two sheets `t ≠ 0` and from a collar chart around `t = 0`.
* Quarter circles from `1` to `i` and from `1` to `j` in `S³` give loops in
  each sheet, hence two pairs `(a₁, b₁)` and `(a₂, b₂)` in the fundamental
  group with `a² = b²` and `b a = a⁻¹ b`; the relations come from explicit
  homotopies in `S³` that avoid the removed balls. A map collapsing the lower
  sheet onto a ball, together with the monodromy of the covering
  `S³ → S³/Q₈`, shows `a₁² ≠ 1`, `a₂² ≠ 1` and `a₁² ≠ a₂²`.
* A faithful representation in `GL(4, ℝ)` would send both `a₁²` and `a₂²` to
  `-1`, contradicting `a₁² ≠ a₂²`.
-/

@[expose] public section

open Quaternion Metric Set Topology

namespace MathlibExt.Topology.NonlinearThreeManifoldGroupWanted
namespace Topology

open Matrix

set_option linter.dupNamespace false in
/-- **Closed topological 3-manifold.** A closed topological 3-manifold is a nonempty, compact,
connected, Hausdorff, second-countable topological space $M$ together with an atlas of charts,
homeomorphisms from open subsets of $M$ onto open subsets of $\mathbb{R}^3$, whose domains cover
$M$. Since the charts land in $\mathbb{R}^3$ itself rather than in a half-space, $M$ has no
boundary. -/
structure Closed3Manifold where
  /-- The underlying point set. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier]
  [compact : CompactSpace carrier]
  [connected : ConnectedSpace carrier]
  /-- The carrier is nonempty: a closed manifold has points. -/
  [nonempty : Nonempty carrier]

attribute [instance] Closed3Manifold.topology Closed3Manifold.t2
  Closed3Manifold.secondCountable Closed3Manifold.charted Closed3Manifold.compact
  Closed3Manifold.connected Closed3Manifold.nonempty

namespace QuaternionicDouble

noncomputable section

/-! ## Unit quaternions and the quaternion group -/

/-- The unit sphere of the quaternions, a compact topological group. -/
private abbrev S3 : Type := Metric.sphere (0 : ℍ[ℝ]) 1

private instance factFinrank : Fact (Module.finrank ℝ ℍ[ℝ] = 3 + 1) :=
  ⟨by rw [Quaternion.finrank_eq_four]⟩

/-- A unit quaternion from a quaternion of norm one. -/
private def mkS3 (q : ℍ[ℝ]) (h : ‖q‖ = 1) : S3 := ⟨q, by simpa using h⟩

/-- The norm of a quaternion given by its coordinates. -/
private theorem q_norm_mk (a b c d : ℝ) :
    ‖(⟨a, b, c, d⟩ : ℍ[ℝ])‖ = √(a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  rw [norm_eq_sqrt_real_inner, Quaternion.inner_self, Quaternion.normSq_def']

private theorem q_normSq_coe (x : S3) : Quaternion.normSq (x : ℍ[ℝ]) = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self, norm_eq_of_mem_sphere x, mul_one]

/-- The inverse of a unit quaternion is its conjugate. -/
private theorem q_coe_inv (x : S3) : ((x⁻¹ : S3) : ℍ[ℝ]) = star (x : ℍ[ℝ]) := by
  rw [Metric.unitSphere.coe_inv, Quaternion.inv_def, q_normSq_coe, inv_one, one_smul]

private theorem q_sq_sum (x : S3) : (x : ℍ[ℝ]).re ^ 2 + (x : ℍ[ℝ]).imI ^ 2 + (x : ℍ[ℝ]).imJ ^ 2 +
    (x : ℍ[ℝ]).imK ^ 2 = 1 := by
  rw [← Quaternion.normSq_def', q_normSq_coe]

/-- The quaternion group `Q₈`: unit quaternions with integer coordinates. -/
private def Q8 : Subgroup S3 where
  carrier := {v | (v : ℍ[ℝ]).re ∈ range ((↑) : ℤ → ℝ) ∧ (v : ℍ[ℝ]).imI ∈ range ((↑) : ℤ → ℝ) ∧
    (v : ℍ[ℝ]).imJ ∈ range ((↑) : ℤ → ℝ) ∧ (v : ℍ[ℝ]).imK ∈ range ((↑) : ℤ → ℝ)}
  mul_mem' := by
    rintro a b ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩, ⟨a3, ha3⟩, ⟨a4, ha4⟩⟩
      ⟨⟨b1, hb1⟩, ⟨b2, hb2⟩, ⟨b3, hb3⟩, ⟨b4, hb4⟩⟩
    simp only [Set.mem_ofPred_eq, Metric.unitSphere.coe_mul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, ← ha1, ← ha2, ← ha3, ← ha4,
      ← hb1, ← hb2, ← hb3, ← hb4]
    exact ⟨⟨a1 * b1 - a2 * b2 - a3 * b3 - a4 * b4, by push_cast; ring⟩,
      ⟨a1 * b2 + a2 * b1 + a3 * b4 - a4 * b3, by push_cast; ring⟩,
      ⟨a1 * b3 - a2 * b4 + a3 * b1 + a4 * b2, by push_cast; ring⟩,
      ⟨a1 * b4 + a2 * b3 - a3 * b2 + a4 * b1, by push_cast; ring⟩⟩
  one_mem' := ⟨⟨1, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩⟩
  inv_mem' := by
    rintro x ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩, ⟨a3, ha3⟩, ⟨a4, ha4⟩⟩
    simp only [Set.mem_ofPred_eq, q_coe_inv, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, ← ha1, ← ha2, ← ha3, ← ha4]
    exact ⟨⟨a1, rfl⟩, ⟨-a2, by push_cast; ring⟩, ⟨-a3, by push_cast; ring⟩,
      ⟨-a4, by push_cast; ring⟩⟩

/-- The quaternionic space form `S³/Q₈` (left cosets `v Q₈`). -/
private abbrev Q : Type := S3 ⧸ Q8

/-- The projection `S³ → S³/Q₈`. -/
private abbrev proj : S3 → Q := QuotientGroup.mk

private theorem q_int_mem_of_sq_le_one {x : ℝ} (hx : x ∈ range ((↑) : ℤ → ℝ)) (h : x ^ 2 ≤ 1) :
    x ∈ ({-1, 0, 1} : Set ℝ) := by
  obtain ⟨n, rfl⟩ := hx
  have h' : n ^ 2 ≤ 1 := by exact_mod_cast h
  have h1 : -1 ≤ n := by nlinarith
  have h2 : n ≤ 1 := by nlinarith
  interval_cases n <;> simp

/-- `Q₈` is finite: its coordinates lie in `{-1, 0, 1}`. -/
private theorem q_Q8_finite : (Q8 : Set S3).Finite := by
  have hT : ({-1, 0, 1} : Set ℝ).Finite := Set.toFinite _
  let f : S3 → ℝ × ℝ × ℝ × ℝ := fun v =>
    ((v : ℍ[ℝ]).re, (v : ℍ[ℝ]).imI, (v : ℍ[ℝ]).imJ, (v : ℍ[ℝ]).imK)
  have hf : Function.Injective f := by
    intro v w h
    simp only [f, Prod.mk.injEq] at h
    exact Subtype.ext (Quaternion.ext _ _ h.1 h.2.1 h.2.2.1 h.2.2.2)
  refine Set.Finite.of_finite_image (f := f) ?_ hf.injOn
  refine (hT.prod (hT.prod (hT.prod hT))).subset ?_
  rintro _ ⟨v, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hs := q_sq_sum v
  have e1 := sq_nonneg (v : ℍ[ℝ]).re
  have e2 := sq_nonneg (v : ℍ[ℝ]).imI
  have e3 := sq_nonneg (v : ℍ[ℝ]).imJ
  have e4 := sq_nonneg (v : ℍ[ℝ]).imK
  exact ⟨q_int_mem_of_sq_le_one h1 (by linarith), q_int_mem_of_sq_le_one h2 (by linarith),
    q_int_mem_of_sq_le_one h3 (by linarith), q_int_mem_of_sq_le_one h4 (by linarith)⟩

private theorem Q8_isDiscrete : IsDiscrete (Q8 : Set S3) := q_Q8_finite.isDiscrete

private theorem isQCM : IsQuotientCoveringMap proj Q8.op :=
  Subgroup.isQuotientCoveringMap Q8 Q8_isDiscrete

/-- Charts on `S³/Q₈`, pushed forward from the sphere along the covering map. -/
private instance chartedQ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q :=
  isQCM.isLocalHomeomorph.chartedSpace QuotientGroup.mk_surjective

private instance t2Q : T2Space Q :=
  have : IsClosed (Q8 : Set S3) := q_Q8_finite.isClosed
  QuotientGroup.instT2Space

private theorem q_one_lt_rank : 1 < Module.rank ℝ ℍ[ℝ] := by
  rw [Quaternion.rank_eq_four]; norm_num

private theorem q_connectedSpace_S3 : ConnectedSpace S3 :=
  isConnected_iff_connectedSpace.mp (isConnected_sphere q_one_lt_rank 0 zero_le_one)

private instance connQ : ConnectedSpace Q :=
  have : ConnectedSpace S3 := q_connectedSpace_S3
  QuotientGroup.mk_surjective.connectedSpace continuous_quotient_mk'


/-! ## Special points -/

private theorem norm_eI : ‖(⟨0, 1, 0, 0⟩ : ℍ[ℝ])‖ = 1 := by rw [q_norm_mk]; norm_num
private theorem norm_eJ : ‖(⟨0, 0, 1, 0⟩ : ℍ[ℝ])‖ = 1 := by rw [q_norm_mk]; norm_num
private theorem norm_eK : ‖(⟨0, 0, 0, 1⟩ : ℍ[ℝ])‖ = 1 := by rw [q_norm_mk]; norm_num
private theorem norm_pt : ‖(⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : ℍ[ℝ])‖ = 1 := by rw [q_norm_mk]; norm_num

/-- The unit quaternion `i`. -/
private def eI : S3 := mkS3 ⟨0, 1, 0, 0⟩ norm_eI
/-- The unit quaternion `j`. -/
private def eJ : S3 := mkS3 ⟨0, 0, 1, 0⟩ norm_eJ
/-- The unit quaternion `k`. -/
private def eK : S3 := mkS3 ⟨0, 0, 0, 1⟩ norm_eK
/-- The point `(1 + i + j + k) / 2`, centre of the removed ball. -/
private def pt : S3 := mkS3 ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ norm_pt

/-- The centre of the removed ball in `S³/Q₈`. -/
private def qp : Q := proj pt

/-! ## A chart at `qp` and the radii -/

/-- The model space `ℝ³`. -/
private abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The chart of `S³/Q₈` at `qp`. -/
private def φ : OpenPartialHomeomorph Q E3 := chartAt E3 qp

/-- The image of `qp` in the chart. -/
private def c₀ : E3 := φ qp

/-- The safe set: unit quaternions with a vanishing coordinate. It avoids the orbit `pt · Q₈`. -/
private def Zs : Set S3 :=
  {v | (v : ℍ[ℝ]).re = 0 ∨ (v : ℍ[ℝ]).imI = 0 ∨ (v : ℍ[ℝ]).imJ = 0 ∨ (v : ℍ[ℝ]).imK = 0}

/-- The image of the safe set in `S³/Q₈`. -/
private def K : Set Q := proj '' Zs

/-- The coordinates of an integer unit quaternion have odd sum. -/
private theorem fpart_sum_odd {n₀ n₁ n₂ n₃ : ℤ} (h : n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = 1) :
    (n₀ + n₁ + n₂ + n₃) % 2 = 1 := by
  have e : ∀ n : ℤ, (n ^ 2 - n) % 2 = 0 := fun n => by
    rw [show n ^ 2 - n = n * (n - 1) by ring]
    exact Int.even_iff.mp (Int.even_mul_pred_self n)
  have e₀ := e n₀; have e₁ := e n₁; have e₂ := e n₂; have e₃ := e n₃
  omega

/-- The orbit of `pt` avoids the safe set. -/
private theorem fpart_qp_not_mem_K : qp ∉ K := by
  rintro ⟨v, hv, hvq⟩
  have hmem : pt⁻¹ * v ∈ Q8 := QuotientGroup.eq.mp hvq.symm
  set h := pt⁻¹ * v with hh
  have hv' : v = pt * h := by rw [hh, mul_inv_cancel_left]
  obtain ⟨⟨n₀, h₀⟩, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, ⟨n₃, h₃⟩⟩ := hmem
  have hnorm : ‖(h : ℍ[ℝ])‖ = 1 := by simp
  have hsq : (n₀ : ℝ) ^ 2 + n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = 1 := by
    have := Quaternion.normSq_eq_norm_mul_self (h : ℍ[ℝ])
    rw [hnorm, Quaternion.normSq_def'] at this
    rw [h₀, h₁, h₂, h₃]; linarith
  have hsqZ : n₀ ^ 2 + n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = 1 := by exact_mod_cast hsq
  have hpt : (pt : ℍ[ℝ]) = ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ := rfl
  have hvq' : (v : ℍ[ℝ]) = (pt : ℍ[ℝ]) * (h : ℍ[ℝ]) := by rw [hv']; rfl
  have hodd := fpart_sum_odd hsqZ
  have hv2 : (v : ℍ[ℝ]).re = 0 ∨ (v : ℍ[ℝ]).imI = 0 ∨ (v : ℍ[ℝ]).imJ = 0 ∨
      (v : ℍ[ℝ]).imK = 0 := hv
  rw [hvq', hpt] at hv2
  rcases hv2 with hz | hz | hz | hz
  · simp only [Quaternion.re_mul] at hz
    rw [← h₀, ← h₁, ← h₂, ← h₃] at hz
    have : ((n₀ - n₁ - n₂ - n₃ : ℤ) : ℝ) = 0 := by push_cast; linarith
    have : n₀ - n₁ - n₂ - n₃ = 0 := by exact_mod_cast this
    omega
  · simp only [Quaternion.imI_mul] at hz
    rw [← h₀, ← h₁, ← h₂, ← h₃] at hz
    have : ((n₀ + n₁ - n₂ + n₃ : ℤ) : ℝ) = 0 := by push_cast; linarith
    have : n₀ + n₁ - n₂ + n₃ = 0 := by exact_mod_cast this
    omega
  · simp only [Quaternion.imJ_mul] at hz
    rw [← h₀, ← h₁, ← h₂, ← h₃] at hz
    have : ((n₀ + n₁ + n₂ - n₃ : ℤ) : ℝ) = 0 := by push_cast; linarith
    have : n₀ + n₁ + n₂ - n₃ = 0 := by exact_mod_cast this
    omega
  · simp only [Quaternion.imK_mul] at hz
    rw [← h₀, ← h₁, ← h₂, ← h₃] at hz
    have : ((n₀ - n₁ + n₂ + n₃ : ℤ) : ℝ) = 0 := by push_cast; linarith
    have : n₀ - n₁ + n₂ + n₃ = 0 := by exact_mod_cast this
    omega

/-- The image of the safe set is compact. -/
private theorem fpart_isCompact_K : IsCompact K := by
  have hc : Continuous fun v : S3 => (v : ℍ[ℝ]) := continuous_subtype_val
  have hZ : IsClosed Zs := by
    have hset : Zs = {v : S3 | (v : ℍ[ℝ]).re = 0} ∪ ({v | (v : ℍ[ℝ]).imI = 0} ∪
        ({v | (v : ℍ[ℝ]).imJ = 0} ∪ {v | (v : ℍ[ℝ]).imK = 0})) :=
      Set.ext fun _ => Iff.rfl
    rw [hset]
    exact (isClosed_eq (Quaternion.continuous_re.comp hc) continuous_const).union
      ((isClosed_eq (Quaternion.continuous_imI.comp hc) continuous_const).union
      ((isClosed_eq (Quaternion.continuous_imJ.comp hc) continuous_const).union
      (isClosed_eq (Quaternion.continuous_imK.comp hc) continuous_const)))
  exact hZ.isCompact.image QuotientGroup.continuous_mk

private theorem exists_radius : ∃ R : ℝ, 0 < R ∧ R < 1 ∧ closedBall c₀ R ⊆ φ.target ∧
    ∀ q ∈ K, q ∈ φ.source → R < dist (φ q) c₀ := by
  have hc₀ : c₀ ∈ φ.target := mem_chart_target E3 qp
  obtain ⟨R₀, hR₀, hball⟩ := Metric.isOpen_iff.mp φ.open_target c₀ hc₀
  have hKc : IsClosed K := fpart_isCompact_K.isClosed
  have hcont : ContinuousAt φ.symm c₀ := φ.continuousAt_symm hc₀
  have hnhds : Kᶜ ∈ 𝓝 (φ.symm c₀) := by
    have h : φ.symm c₀ = qp := φ.left_inv (mem_chart_source E3 qp)
    rw [h]
    exact hKc.isOpen_compl.mem_nhds fpart_qp_not_mem_K
  obtain ⟨r₁, hr₁, hr₁K⟩ := Metric.mem_nhds_iff.mp (hcont hnhds)
  refine ⟨min (min R₀ r₁) 1 / 2, by positivity, by
    linarith [min_le_right (min R₀ r₁) 1], ?_, ?_⟩
  · intro w hw
    apply hball
    rw [mem_ball]
    rw [mem_closedBall] at hw
    have : min (min R₀ r₁) 1 ≤ R₀ := (min_le_left _ _).trans (min_le_left _ _)
    linarith [show 0 < min (min R₀ r₁) 1 by positivity]
  · intro q hq hs
    by_contra hlt
    replace hlt := not_lt.mp hlt
    have hlt' : dist (φ q) c₀ < r₁ := by
      have : min (min R₀ r₁) 1 ≤ r₁ := (min_le_left _ _).trans (min_le_right _ _)
      linarith [show 0 < min (min R₀ r₁) 1 by positivity]
    have := hr₁K (mem_ball.mpr hlt')
    rw [mem_preimage, φ.left_inv hs] at this
    exact this hq

/-- The outer radius. -/
private def R : ℝ := exists_radius.choose
/-- The radius of the removed ball. -/
private def r : ℝ := R / 2
/-- The width of the collar used by the charts and the collapse map. -/
private def δ : ℝ := r / 2

private theorem R_pos : 0 < R := exists_radius.choose_spec.1
private theorem R_lt_one : R < 1 := exists_radius.choose_spec.2.1
private theorem closedBall_subset_target : closedBall c₀ R ⊆ φ.target :=
  exists_radius.choose_spec.2.2.1
private theorem lt_dist_of_mem_K {q : Q} (hq : q ∈ K) (hs : q ∈ φ.source) : R < dist (φ q) c₀ :=
  exists_radius.choose_spec.2.2.2 q hq hs

/-- The gluing function: negative exactly on the removed open ball. -/
private def f (q : Q) : ℝ := by
  classical exact if q ∈ φ.source then min (dist (φ q) c₀) R - r else R - r

private theorem r_pos : 0 < r := by unfold r; linarith [R_pos]
private theorem δ_pos : 0 < δ := by unfold δ; linarith [r_pos]
private theorem δ_lt_r : δ < r := by unfold δ; linarith [r_pos]
private theorem r_lt_R : r < R := by unfold r; linarith [R_pos]
private theorem R_sub_r : R - r = r := by unfold r; ring
private theorem δ_sq_lt : δ ^ 2 < R - r := by
  rw [R_sub_r]; unfold δ
  have h1 : r < 1 := by unfold r; linarith [R_lt_one]
  nlinarith [r_pos]

private theorem qp_mem_source : qp ∈ φ.source := mem_chart_source E3 qp
private theorem φ_symm_c₀ : φ.symm c₀ = qp := φ.left_inv qp_mem_source
private theorem closedBall_r_subset_target : closedBall c₀ r ⊆ φ.target :=
  (closedBall_subset_closedBall r_lt_R.le).trans closedBall_subset_target

private theorem f_le (q : Q) : f q ≤ R - r := by
  unfold f; split_ifs
  · linarith [min_le_right (dist (φ q) c₀) R]
  · exact le_rfl

/-- Below its maximum, `f` is the distance to `c₀` in the chart, minus `r`. -/
private theorem f_spec {q : Q} (h : f q < R - r) : q ∈ φ.source ∧ dist (φ q) c₀ = f q + r := by
  unfold f at h ⊢
  split_ifs at h ⊢ with hs
  · refine ⟨hs, ?_⟩
    have : min (dist (φ q) c₀) R < R := by linarith
    rw [min_eq_left (min_lt_iff.mp this |>.resolve_right (lt_irrefl _)).le]; ring
  · exact absurd h (lt_irrefl _)

private theorem f_of_mem_source {q : Q} (hs : q ∈ φ.source) (h : dist (φ q) c₀ ≤ R) :
    f q = dist (φ q) c₀ - r := by
  unfold f; split_ifs; rw [min_eq_left h]

private theorem f_qp : f qp = -r := by
  rw [f_of_mem_source qp_mem_source (by rw [show φ qp = c₀ from rfl, dist_self]; exact R_pos.le)]
  simp [show φ qp = c₀ from rfl]

private theorem continuous_f : Continuous f := by
  have hcpt : IsCompact (φ.symm '' closedBall c₀ R) :=
    (isCompact_closedBall c₀ R).image_of_continuousOn
      (φ.continuousOn_symm.mono closedBall_subset_target)
  have hsub : φ.symm '' closedBall c₀ R ⊆ φ.source := by
    rintro _ ⟨w, hw, rfl⟩; exact φ.map_target (closedBall_subset_target hw)
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hq : q ∈ φ.source
  · have hev : f =ᶠ[𝓝 q] fun q' => min (dist (φ q') c₀) R - r := by
      filter_upwards [φ.open_source.mem_nhds hq] with q' hq'
      unfold f; simp only [hq', ↓reduceIte]
    refine ContinuousAt.congr ?_ hev.symm
    exact ((((φ.continuousAt hq).dist continuousAt_const).min continuousAt_const).sub
      continuousAt_const)
  · have hq' : q ∈ (φ.symm '' closedBall c₀ R)ᶜ := fun h => hq (hsub h)
    have hev : f =ᶠ[𝓝 q] fun _ => R - r := by
      filter_upwards [hcpt.isClosed.isOpen_compl.mem_nhds hq'] with q' hq''
      unfold f
      split_ifs with hs
      · have : R < dist (φ q') c₀ := by
          by_contra hle
          exact hq'' ⟨φ q', mem_closedBall.mpr (not_lt.mp hle), φ.left_inv hs⟩
        rw [min_eq_right this.le]
      · rfl
    exact continuousAt_const.congr hev.symm

private theorem f_eq_of_mem_K {q : Q} (hq : q ∈ K) : f q = R - r := by
  unfold f
  split_ifs with hs
  · rw [min_eq_right (lt_dist_of_mem_K hq hs).le]
  · rfl

/-- The fibres of `proj` are finite. -/
private theorem q_fiber_finite (v : S3) : (proj ⁻¹' {proj v}).Finite := by
  refine (q_Q8_finite.image (fun g => v * g)).subset ?_
  intro w hw
  have hmem : v⁻¹ * w ∈ Q8 := QuotientGroup.eq.mp (Set.mem_singleton_iff.mp hw).symm
  exact ⟨v⁻¹ * w, hmem, mul_inv_cancel_left v w⟩

private theorem q_one_lt_rank_E3 : 1 < Module.rank ℝ E3 := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num

/-- The complement of a nonempty finite set in `S³` is connected (stereographic projection from
one of its points). -/
private theorem q_isConnected_compl_finite {F : Set S3} (hF : F.Finite) {N : S3} (hN : N ∈ F) :
    IsConnected Fᶜ := by
  let e := stereographic' 3 N
  have hconn : IsConnected (e '' (F \ {N}))ᶜ :=
    (((hF.sdiff (t := {N})).image e).countable).isConnected_compl_of_one_lt_rank q_one_lt_rank_E3
  have heq : Fᶜ = e.symm '' (e '' (F \ {N}))ᶜ := by
    ext x
    constructor
    · intro hx
      have hxs : x ∈ e.source := by
        rw [stereographic'_source]
        rintro rfl
        exact hx hN
      refine ⟨e x, ?_, e.left_inv hxs⟩
      rintro ⟨y, ⟨hyF, hyN⟩, hxy⟩
      have hys : y ∈ e.source := by rw [stereographic'_source]; exact hyN
      exact hx (e.injOn hys hxs hxy ▸ hyF)
    · rintro ⟨z, hz, rfl⟩ hzF
      have hzt : z ∈ e.target := by rw [stereographic'_target]; trivial
      have hs : e.symm z ∈ e.source := e.map_target hzt
      rw [stereographic'_source] at hs
      exact hz ⟨e.symm z, ⟨hzF, hs⟩, e.right_inv hzt⟩
  rw [heq]
  refine hconn.image _ (e.continuousOn_symm.mono ?_)
  rw [stereographic'_target]
  exact subset_univ _

/-- `S³/Q₈` minus the centre of the removed ball is connected. -/
private theorem isConnected_compl_qp : IsConnected ({qp}ᶜ : Set Q) := by
  have h1 : IsConnected (proj ⁻¹' {qp})ᶜ := q_isConnected_compl_finite (q_fiber_finite pt) rfl
  have h2 : proj '' (proj ⁻¹' {qp})ᶜ = {qp}ᶜ := by
    rw [Set.image_compl_preimage, QuotientGroup.mk_surjective.range_eq, Set.compl_eq_univ_sdiff]
  rw [← h2]
  exact h1.image _ continuous_quotient_mk'.continuousOn

/-! ## The double -/

/-- The double `{(q, t) | t² = f q}` of `S³/Q₈` minus an open ball: the connected sum of
`S³/Q₈` with its mirror image. -/
private abbrev X : Type := ↥{x : Q × ℝ | x.2 ^ 2 = f x.1}

/-- The unit direction from `c₀` in the chart `φ` (zero at `c₀`). -/
private def dir (q : Q) : E3 := ‖φ q - c₀‖⁻¹ • (φ q - c₀)

/-! ### Charts on the double

Three kinds of charts: on the upper sheet `{0 < t}` and on the lower sheet `{t < 0}` the
projection `(q, t) ↦ q` is a homeomorphism onto `{0 < f}`, which we compose with a chart of `Q`;
near the seam `{t = 0}` we use one collar chart onto the spherical shell
`{r - δ < ‖w‖ < r + δ}` of `E3`, sending `(q, t)` to `(r + t) • dir q`. -/

private theorem xc_eq (y : X) : y.1.2 ^ 2 = f y.1.1 := y.2

private theorem xc_sq_eq {s : ℝ} (hs : s * s = 1) (t : ℝ) : t ^ 2 = (s * t) ^ 2 := by
  rw [mul_pow, sq s, hs, one_mul]

private theorem xc_mem_sheet {s : ℝ} (hs : s * s = 1) {q : Q} (hq : 0 ≤ f q) :
    (q, s * √(f q)) ∈ {x : Q × ℝ | x.2 ^ 2 = f x.1} := by
  change (s * √(f q)) ^ 2 = f q
  rw [← xc_sq_eq hs, Real.sq_sqrt hq]

/-- The section `q ↦ (q, s √(f q))` of the double over `{0 ≤ f}`, with default value `x`. -/
private def xc_sec (x : X) {s : ℝ} (hs : s * s = 1) (q : Q) : X := by
  classical exact if h : 0 ≤ f q then ⟨(q, s * √(f q)), xc_mem_sheet hs h⟩ else x

private theorem xc_sec_of_nonneg (x : X) {s : ℝ} (hs : s * s = 1) {q : Q} (h : 0 ≤ f q) :
    (xc_sec x hs q : Q × ℝ) = (q, s * √(f q)) := by
  simp only [xc_sec, h, ↓reduceDIte]

/-- The projection of the sheet `{0 < s t}` of the double onto `{0 < f}` (for `s = ±1`). -/
private def xc_sheet (x : X) {s : ℝ} (hs : s * s = 1) : OpenPartialHomeomorph X Q where
  toFun y := y.1.1
  invFun := xc_sec x hs
  source := {y | 0 < s * y.1.2}
  target := {q | 0 < f q}
  map_source' y hy := by
    change 0 < f y.1.1
    rw [← xc_eq y, xc_sq_eq hs]
    exact pow_pos hy 2
  map_target' q hq := by
    change 0 < s * (xc_sec x hs q : Q × ℝ).2
    rw [xc_sec_of_nonneg x hs (le_of_lt hq), ← mul_assoc, hs, one_mul]
    exact Real.sqrt_pos.2 hq
  left_inv' y hy := by
    have hy' : 0 < s * y.1.2 := hy
    apply Subtype.ext
    rw [xc_sec_of_nonneg x hs (by rw [← xc_eq y]; positivity), ← xc_eq y, xc_sq_eq hs,
      Real.sqrt_sq hy'.le, ← mul_assoc, hs, one_mul]
  right_inv' q hq := by
    show (xc_sec x hs q : Q × ℝ).1 = q
    rw [xc_sec_of_nonneg x hs (le_of_lt hq)]
  open_source := isOpen_lt continuous_const (by fun_prop)
  open_target := isOpen_lt continuous_const continuous_f
  continuousOn_toFun := (by fun_prop : Continuous fun y : X => y.1.1).continuousOn
  continuousOn_invFun := by
    rw [IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (f := fun q => (q, s * √(f q))) ?_ ?_
    · exact (continuous_id.prodMk
        (continuous_const.mul (Real.continuous_sqrt.comp continuous_f))).continuousOn
    · intro q hq
      exact xc_sec_of_nonneg x hs (le_of_lt hq)

/-- The chart on the sheet `{0 < s t}`, through the chart of `Q` at `x.1.1`. -/
private def xc_chartA (x : X) {s : ℝ} (hs : s * s = 1) : OpenPartialHomeomorph X E3 :=
  (xc_sheet x hs).trans (chartAt E3 x.1.1)

private theorem xc_mem_chartA (x : X) {s : ℝ} (hs : s * s = 1) (h : 0 < s * x.1.2) :
    x ∈ (xc_chartA x hs).source := by
  rw [xc_chartA, OpenPartialHomeomorph.trans_source]
  exact ⟨h, mem_chart_source E3 x.1.1⟩

/-- The source of the collar chart. -/
private def xc_UB : Set X := {y | y.1.1 ∈ φ.source ∧ |y.1.2| < δ}

/-- The target of the collar chart: a spherical shell around `0`. -/
private def xc_VB : Set E3 := {w | r - δ < ‖w‖ ∧ ‖w‖ < r + δ}

/-- The point of the chart `φ` used by the inverse of the collar chart. -/
private def xc_pt (w : E3) : E3 := c₀ + (r + (‖w‖ - r) ^ 2) • (‖w‖⁻¹ • w)

private theorem xc_norm_pos {w : E3} (hw : w ∈ xc_VB) : 0 < ‖w‖ := by
  have := hw.1
  linarith [δ_lt_r]

private theorem xc_sq_lt {w : E3} (hw : w ∈ xc_VB) : (‖w‖ - r) ^ 2 < δ ^ 2 :=
  sq_lt_sq' (by linarith [hw.1]) (by linarith [hw.2])

private theorem xc_dist_pt {w : E3} (hw : w ∈ xc_VB) : dist (xc_pt w) c₀ = r + (‖w‖ - r) ^ 2 := by
  have hn := xc_norm_pos hw
  rw [xc_pt, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ hn.ne', mul_one, Real.norm_eq_abs,
    abs_of_pos (add_pos_of_pos_of_nonneg r_pos (sq_nonneg _))]

private theorem xc_dist_pt_lt {w : E3} (hw : w ∈ xc_VB) : r + (‖w‖ - r) ^ 2 < R := by
  linarith [xc_sq_lt hw, δ_sq_lt]

private theorem xc_pt_mem_target {w : E3} (hw : w ∈ xc_VB) : xc_pt w ∈ φ.target :=
  closedBall_subset_target (mem_closedBall.2 ((xc_dist_pt hw).le.trans (xc_dist_pt_lt hw).le))

private theorem xc_f_pt {w : E3} (hw : w ∈ xc_VB) : f (φ.symm (xc_pt w)) = (‖w‖ - r) ^ 2 := by
  have ht := xc_pt_mem_target hw
  rw [f_of_mem_source (φ.map_target ht)
    (by rw [φ.right_inv ht, xc_dist_pt hw]; exact (xc_dist_pt_lt hw).le),
    φ.right_inv ht, xc_dist_pt hw]
  ring

private theorem xc_invB_mem {w : E3} (hw : w ∈ xc_VB) :
    (φ.symm (xc_pt w), ‖w‖ - r) ∈ {x : Q × ℝ | x.2 ^ 2 = f x.1} := by
  change (‖w‖ - r) ^ 2 = f (φ.symm (xc_pt w))
  rw [xc_f_pt hw]

/-- The inverse of the collar chart, with default value `x` outside the shell. -/
private def xc_invB (x : X) (w : E3) : X := by
  classical exact if h : w ∈ xc_VB then ⟨(φ.symm (xc_pt w), ‖w‖ - r), xc_invB_mem h⟩ else x

private theorem xc_invB_of_mem (x : X) {w : E3} (hw : w ∈ xc_VB) :
    (xc_invB x w : Q × ℝ) = (φ.symm (xc_pt w), ‖w‖ - r) := by
  simp only [xc_invB, hw, ↓reduceDIte]

private theorem xc_spec_UB {y : X} (hy : |y.1.2| < δ) :
    y.1.1 ∈ φ.source ∧ dist (φ y.1.1) c₀ = y.1.2 ^ 2 + r := by
  have hf : f y.1.1 < R - r := by
    rw [← xc_eq y]
    have := abs_lt.1 hy
    nlinarith [δ_sq_lt]
  have h := f_spec hf
  rwa [← xc_eq y] at h

private theorem xc_r_add_pos {y : X} (hy : |y.1.2| < δ) : 0 < r + y.1.2 := by
  linarith [(abs_lt.1 hy).1, δ_lt_r]

private theorem xc_ne_c₀ {y : X} (hy : |y.1.2| < δ) : φ y.1.1 ≠ c₀ := by
  intro he
  have h := (xc_spec_UB hy).2
  rw [he, dist_self] at h
  nlinarith [r_pos, sq_nonneg y.1.2]

private theorem xc_norm_toB {y : X} (hy : |y.1.2| < δ) :
    ‖(r + y.1.2) • dir y.1.1‖ = r + y.1.2 := by
  rw [dir, norm_smul, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 (sub_ne_zero.2 (xc_ne_c₀ hy))), mul_one,
    Real.norm_eq_abs, abs_of_pos (xc_r_add_pos hy)]

private theorem xc_toB_mem {y : X} (hy : |y.1.2| < δ) : (r + y.1.2) • dir y.1.1 ∈ xc_VB := by
  have h := abs_lt.1 hy
  refine ⟨?_, ?_⟩ <;> rw [xc_norm_toB hy] <;> linarith

private theorem xc_invB_toB (x : X) {y : X} (hy : y ∈ xc_UB) :
    xc_invB x ((r + y.1.2) • dir y.1.1) = y := by
  have hy2 : |y.1.2| < δ := hy.2
  have hpos := xc_r_add_pos hy2
  have hd := (xc_spec_UB hy2).2
  have hpt : xc_pt ((r + y.1.2) • dir y.1.1) = φ y.1.1 := by
    rw [xc_pt, xc_norm_toB hy2, add_sub_cancel_left, inv_smul_smul₀ hpos.ne', dir,
      ← dist_eq_norm, hd, smul_smul, show (r + y.1.2 ^ 2) * (y.1.2 ^ 2 + r)⁻¹ = 1 by
        rw [add_comm r]; exact mul_inv_cancel₀ (add_pos_of_nonneg_of_pos (sq_nonneg _) r_pos).ne',
      one_smul, add_sub_cancel]
  apply Subtype.ext
  rw [xc_invB_of_mem x (xc_toB_mem hy2), hpt, φ.left_inv hy.1, xc_norm_toB hy2,
    add_sub_cancel_left]

private theorem xc_toB_invB (x : X) {w : E3} (hw : w ∈ xc_VB) :
    (r + (xc_invB x w : Q × ℝ).2) • dir (xc_invB x w : Q × ℝ).1 = w := by
  have ht := xc_pt_mem_target hw
  have hn := xc_norm_pos hw
  have hρ : 0 < r + (‖w‖ - r) ^ 2 := add_pos_of_pos_of_nonneg r_pos (sq_nonneg _)
  rw [xc_invB_of_mem x hw, add_sub_cancel, dir, φ.right_inv ht, ← dist_eq_norm,
    xc_dist_pt hw, xc_pt, add_sub_cancel_left, inv_smul_smul₀ hρ.ne', smul_inv_smul₀ hn.ne']

private theorem xc_isOpen_UB : IsOpen xc_UB := by
  have h1 : Continuous fun y : X => y.1.1 := by fun_prop
  have h2 : Continuous fun y : X => |y.1.2| := by fun_prop
  exact (φ.open_source.preimage h1).inter (isOpen_lt h2 continuous_const)

private theorem xc_isOpen_VB : IsOpen xc_VB :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

private theorem xc_continuousOn_toB :
    ContinuousOn (fun y : X => (r + y.1.2) • dir y.1.1) xc_UB := by
  have h1 : ContinuousOn (fun y : X => φ y.1.1 - c₀) xc_UB :=
    (φ.continuousOn.comp (by fun_prop : Continuous fun y : X => y.1.1).continuousOn
      (fun y (hy : y ∈ xc_UB) => hy.1)).sub continuousOn_const
  have h2 : ∀ y ∈ xc_UB, ‖φ y.1.1 - c₀‖ ≠ 0 := fun y hy =>
    norm_ne_zero_iff.2 (sub_ne_zero.2 (xc_ne_c₀ hy.2))
  exact (by fun_prop : Continuous fun y : X => r + y.1.2).continuousOn.smul
    (h1.norm.inv₀ h2 |>.smul h1)

private theorem xc_continuousOn_invB (x : X) : ContinuousOn (xc_invB x) xc_VB := by
  rw [IsInducing.subtypeVal.continuousOn_iff]
  refine ContinuousOn.congr (f := fun w => (φ.symm (xc_pt w), ‖w‖ - r)) ?_ ?_
  · refine ContinuousOn.prodMk ?_ (continuous_norm.sub continuous_const).continuousOn
    refine φ.continuousOn_symm.comp ?_ (fun w hw => xc_pt_mem_target hw)
    have h2 : ∀ w ∈ xc_VB, ‖w‖ ≠ 0 := fun w hw => (xc_norm_pos hw).ne'
    exact continuousOn_const.add
      ((by fun_prop : Continuous fun w : E3 => r + (‖w‖ - r) ^ 2).continuousOn.smul
        (continuous_norm.continuousOn.inv₀ h2 |>.smul continuousOn_id))
  · intro w hw
    exact xc_invB_of_mem x hw

/-- The collar chart around the seam `{t = 0}`, with default value `x` outside the shell. -/
private def xc_chartB (x : X) : OpenPartialHomeomorph X E3 where
  toFun y := (r + y.1.2) • dir y.1.1
  invFun := xc_invB x
  source := xc_UB
  target := xc_VB
  map_source' _ hy := xc_toB_mem hy.2
  map_target' w hw := by
    refine ⟨?_, ?_⟩
    · rw [xc_invB_of_mem x hw]
      exact φ.map_target (xc_pt_mem_target hw)
    · rw [xc_invB_of_mem x hw]
      exact abs_sub_lt_iff.2 ⟨by linarith [hw.2], by linarith [hw.1]⟩
  left_inv' _ hy := xc_invB_toB x hy
  right_inv' _ hw := xc_toB_invB x hw
  open_source := xc_isOpen_UB
  open_target := xc_isOpen_VB
  continuousOn_toFun := xc_continuousOn_toB
  continuousOn_invFun := xc_continuousOn_invB x

private theorem xc_mem_UB {x : X} (h : x.1.2 = 0) : x ∈ xc_UB := by
  have hx : |x.1.2| < δ := by rw [h, abs_zero]; exact δ_pos
  exact ⟨(xc_spec_UB hx).1, hx⟩

/-- The preferred chart at a point of the double. -/
private def xc_chartAt (x : X) : OpenPartialHomeomorph X E3 := by
  classical exact
    if 0 < x.1.2 then xc_chartA x (s := 1) (by norm_num)
    else if x.1.2 < 0 then xc_chartA x (s := -1) (by norm_num)
    else xc_chartB x

private theorem xc_mem_chart_source (x : X) : x ∈ (xc_chartAt x).source := by
  unfold xc_chartAt
  split_ifs with h1 h2
  · exact xc_mem_chartA x _ (by rw [one_mul]; exact h1)
  · exact xc_mem_chartA x _ (by linarith)
  · exact xc_mem_UB (le_antisymm (not_lt.mp h1) (not_lt.mp h2))

private instance chartedX : ChartedSpace E3 X where
  atlas := range xc_chartAt
  chartAt := xc_chartAt
  mem_chart_source := xc_mem_chart_source
  chart_mem_atlas x := mem_range_self x

/-! ### Compactness and connectedness of the double -/

private theorem xt_isClosed : IsClosed {x : Q × ℝ | x.2 ^ 2 = f x.1} :=
  isClosed_eq (continuous_snd.pow 2) (continuous_f.comp continuous_fst)

private theorem xt_subset_box :
    {x : Q × ℝ | x.2 ^ 2 = f x.1} ⊆ univ ×ˢ Icc (-√(R - r)) (√(R - r)) := fun x hx =>
  ⟨mem_univ _, abs_le.mp (Real.abs_le_sqrt ((le_of_eq hx).trans (f_le x.1)))⟩

private instance compactX : CompactSpace X :=
  isCompact_iff_compactSpace.mp <|
    (isCompact_univ.prod isCompact_Icc).of_isClosed_subset xt_isClosed xt_subset_box

private theorem xt_norm_sub_ne {q : Q} (h : φ q ≠ c₀) : ‖φ q - c₀‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)

private theorem xt_norm_dir {q : Q} (h : φ q ≠ c₀) : ‖dir q‖ = 1 := by
  rw [dir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (xt_norm_sub_ne h)]

private theorem xt_norm_dir_le (q : Q) : ‖dir q‖ ≤ 1 := by
  by_cases h : φ q = c₀
  · simp [dir, h]
  · exact (xt_norm_dir h).le

private theorem xt_add_dist_smul_dir {q : Q} (h : φ q ≠ c₀) :
    c₀ + dist (φ q) c₀ • dir q = φ q := by
  rw [dir, dist_eq_norm_sub, smul_smul, mul_inv_cancel₀ (xt_norm_sub_ne h), one_smul,
    add_sub_cancel]

private theorem xt_dist_add_smul_dir {q : Q} (h : φ q ≠ c₀) {s : ℝ} (hs : 0 ≤ s) :
    dist (c₀ + s • dir q) c₀ = s := by
  rw [dist_eq_norm_sub, add_sub_cancel_left, norm_smul, xt_norm_dir h, mul_one,
    Real.norm_of_nonneg hs]

private theorem xt_continuousAt_dir {q : Q} (hs : q ∈ φ.source) (h : φ q ≠ c₀) :
    ContinuousAt dir q := by
  have hφ : ContinuousAt φ q := φ.continuousAt hs
  have h' := xt_norm_sub_ne h
  unfold dir
  fun_prop (disch := assumption)

private theorem xt_φ_ne {q : Q} (hs : q ∈ φ.source) (hq : q ≠ qp) : φ q ≠ c₀ :=
  fun h => hq (φ.injOn hs qp_mem_source h)

private theorem xt_f_pos_of_notMem {q : Q} (hs : q ∉ φ.source) : 0 < f q := by
  by_contra h
  have h := not_lt.mp h
  exact hs (f_spec (by rw [R_sub_r]; linarith [r_pos])).1

private theorem xt_r_le_dist {q : Q} (hs : q ∈ φ.source) (h : 0 ≤ f q) : r ≤ dist (φ q) c₀ := by
  by_contra hd
  have hd := not_le.mp hd
  rw [f_of_mem_source hs (hd.le.trans r_lt_R.le)] at h
  linarith

private theorem xt_f_nonneg {q : Q} (h : r ≤ dist (φ q) c₀) : 0 ≤ f q := by
  by_contra hf
  have hf := not_le.mp hf
  have := (f_spec (show f q < R - r by rw [R_sub_r]; linarith [r_pos])).2
  linarith

/-- The radial retraction of `S³/Q₈ ∖ {qp}` onto `{q | 0 ≤ f q}`. -/
private def xt_ret (q : Q) : Q := by
  classical exact if q ∈ φ.source then φ.symm (c₀ + max (dist (φ q) c₀) r • dir q) else q

private theorem xt_ret_of_mem {q : Q} (hs : q ∈ φ.source) :
    xt_ret q = φ.symm (c₀ + max (dist (φ q) c₀) r • dir q) := by
  unfold xt_ret; exact ite_eq_left hs

private theorem xt_ret_of_notMem {q : Q} (hs : q ∉ φ.source) : xt_ret q = q := by
  unfold xt_ret; exact ite_eq_right hs

private theorem xt_ret_of_r_le {q : Q} (hs : q ∈ φ.source) (h : r ≤ dist (φ q) c₀) :
    xt_ret q = q := by
  have hne : φ q ≠ c₀ := fun h' => by rw [h', dist_self] at h; linarith [r_pos]
  rw [xt_ret_of_mem hs, max_eq_left h, xt_add_dist_smul_dir hne, φ.left_inv hs]

private theorem xt_ret_arg_mem {q : Q} (hs : q ∈ φ.source) (hq : q ≠ qp) :
    c₀ + max (dist (φ q) c₀) r • dir q ∈ φ.target := by
  rcases le_total r (dist (φ q) c₀) with h | h
  · rw [max_eq_left h, xt_add_dist_smul_dir (xt_φ_ne hs hq)]
    exact φ.map_source hs
  · rw [max_eq_right h]
    apply closedBall_r_subset_target
    rw [mem_closedBall, xt_dist_add_smul_dir (xt_φ_ne hs hq) r_pos.le]

private theorem xt_ret_eq_self {q : Q} (h : 0 ≤ f q) : xt_ret q = q := by
  by_cases hs : q ∈ φ.source
  · exact xt_ret_of_r_le hs (xt_r_le_dist hs h)
  · exact xt_ret_of_notMem hs

private theorem xt_f_ret_nonneg {q : Q} (hq : q ≠ qp) : 0 ≤ f (xt_ret q) := by
  by_cases hs : q ∈ φ.source
  · rw [xt_ret_of_mem hs]
    apply xt_f_nonneg
    rw [φ.right_inv (xt_ret_arg_mem hs hq),
      xt_dist_add_smul_dir (xt_φ_ne hs hq) (r_pos.le.trans (le_max_right _ _))]
    exact le_max_right _ _
  · rw [xt_ret_of_notMem hs]
    exact (xt_f_pos_of_notMem hs).le

private theorem xt_continuousOn_ret : ContinuousOn xt_ret {qp}ᶜ := by
  have hK : IsClosed (φ.symm '' closedBall c₀ r) :=
    ((isCompact_closedBall c₀ r).image_of_continuousOn
      (φ.continuousOn_symm.mono closedBall_r_subset_target)).isClosed
  refine isOpen_compl_singleton.continuousOn_iff.mpr fun q hq => ?_
  have hq : q ≠ qp := hq
  by_cases hs : q ∈ φ.source
  · have heq : (fun y => φ.symm (c₀ + max (dist (φ y) c₀) r • dir y)) =ᶠ[𝓝 q] xt_ret := by
      filter_upwards [φ.open_source.mem_nhds hs] with y hy
      exact (xt_ret_of_mem hy).symm
    refine ContinuousAt.congr ?_ heq
    have hφ : ContinuousAt φ q := φ.continuousAt hs
    have hdir := xt_continuousAt_dir hs (xt_φ_ne hs hq)
    have harg : ContinuousAt (fun y => c₀ + max (dist (φ y) c₀) r • dir y) q := by
      fun_prop
    exact (φ.continuousAt_symm (xt_ret_arg_mem hs hq)).comp_of_eq harg rfl
  · have hq' : q ∉ φ.symm '' closedBall c₀ r := by
      rintro ⟨p, hp, rfl⟩
      exact hs (φ.map_target (closedBall_r_subset_target hp))
    have heq : (fun y => y) =ᶠ[𝓝 q] xt_ret := by
      filter_upwards [(isOpen_compl_iff.mpr hK).mem_nhds hq'] with y hy
      by_cases hys : y ∈ φ.source
      · refine (xt_ret_of_r_le hys ?_).symm
        by_contra hd
        exact hy ⟨φ y, mem_closedBall.mpr (not_le.mp hd).le, φ.left_inv hys⟩
      · exact (xt_ret_of_notMem hys).symm
    exact (continuousAt_id' q).congr heq

private theorem xt_ret_image : xt_ret '' {qp}ᶜ = {q : Q | 0 ≤ f q} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact xt_f_ret_nonneg hp
  · intro hq
    have hq : 0 ≤ f q := hq
    refine ⟨q, fun h => ?_, xt_ret_eq_self hq⟩
    rw [mem_singleton_iff.mp h, f_qp] at hq
    linarith [r_pos]

private theorem xt_isConnected_Y : IsConnected {q : Q | 0 ≤ f q} := by
  rw [← xt_ret_image]
  exact isConnected_compl_qp.image xt_ret xt_continuousOn_ret

private theorem xt_exists_f_eq_zero : ∃ q : Q, f q = 0 := by
  obtain ⟨v, hv⟩ := exists_norm_eq E3 r_pos.le
  have hp : c₀ + v ∈ φ.target := closedBall_r_subset_target (by
    rw [mem_closedBall, dist_eq_norm_sub, add_sub_cancel_left, hv])
  have hd : dist (φ (φ.symm (c₀ + v))) c₀ = r := by
    rw [φ.right_inv hp, dist_eq_norm_sub, add_sub_cancel_left, hv]
  exact ⟨φ.symm (c₀ + v), by
    rw [f_of_mem_source (φ.map_target hp) (hd.le.trans r_lt_R.le), hd, sub_self]⟩

private theorem xt_eq_union : {x : Q × ℝ | x.2 ^ 2 = f x.1} =
    (fun q : Q => (q, √(f q))) '' {q | 0 ≤ f q} ∪
      (fun q : Q => (q, -√(f q))) '' {q | 0 ≤ f q} := by
  ext ⟨q, t⟩
  simp only [mem_ofPred_eq, mem_union, mem_image, Prod.mk.injEq]
  constructor
  · intro h
    have hf : 0 ≤ f q := by rw [← h]; exact sq_nonneg t
    rcases le_or_gt 0 t with ht | ht
    · exact Or.inl ⟨q, hf, rfl, by rw [← h, Real.sqrt_sq ht]⟩
    · exact Or.inr ⟨q, hf, rfl, by rw [← h, Real.sqrt_sq_eq_abs, abs_of_neg ht, neg_neg]⟩
  · rintro (⟨q', hq', rfl, rfl⟩ | ⟨q', hq', rfl, rfl⟩)
    · exact Real.sq_sqrt hq'
    · rw [neg_sq]
      exact Real.sq_sqrt hq'

private instance connX : ConnectedSpace X := by
  have hup : Continuous fun q : Q => (q, √(f q)) :=
    continuous_id.prodMk (Real.continuous_sqrt.comp continuous_f)
  have hlo : Continuous fun q : Q => (q, -√(f q)) :=
    continuous_id.prodMk (Real.continuous_sqrt.comp continuous_f).neg
  obtain ⟨q₁, hq₁⟩ := xt_exists_f_eq_zero
  have hq₁' : q₁ ∈ {q : Q | 0 ≤ f q} := by
    change 0 ≤ f q₁
    rw [hq₁]
  have hne : ((fun q : Q => (q, √(f q))) '' {q | 0 ≤ f q} ∩
      (fun q : Q => (q, -√(f q))) '' {q | 0 ≤ f q}).Nonempty :=
    ⟨(q₁, 0), ⟨q₁, hq₁', by simp [hq₁]⟩, ⟨q₁, hq₁', by simp [hq₁]⟩⟩
  have h := IsConnected.union hne (xt_isConnected_Y.image _ hup.continuousOn)
    (xt_isConnected_Y.image _ hlo.continuousOn)
  rw [← xt_eq_union] at h
  exact isConnected_iff_connectedSpace.mp h


/-! ## The collapse map `ψ : X → S³/Q₈` -/

/-- Radial profile of the collapse map on the lower sheet. -/
private def lam (t : ℝ) : ℝ := r * max 0 (1 + t / δ)

/-- The collapse map: identity on the upper sheet, the lower sheet is pushed into the
removed ball (everything with `t ≤ -δ` goes to `qp`). -/
private def ψfun (x : X) : Q := by
  classical exact if 0 ≤ x.1.2 then x.1.1 else φ.symm (c₀ + lam x.1.2 • dir x.1.1)

/-! ### Continuity of the collapse map -/

private theorem xt_lam_eq_zero {t : ℝ} (ht : t ≤ -δ) : lam t = 0 := by
  have h : t / δ ≤ -1 := (div_le_iff₀ δ_pos).mpr (by linarith)
  rw [lam, max_eq_left (by linarith), mul_zero]

private theorem xt_lam_zero : lam 0 = r := by
  rw [lam, zero_div, add_zero, max_eq_right zero_le_one, mul_one]

private theorem xt_lam_nonneg (t : ℝ) : 0 ≤ lam t := mul_nonneg r_pos.le (le_max_left _ _)

private theorem xt_lam_le {t : ℝ} (ht : t ≤ 0) : lam t ≤ r := by
  have h : t / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht δ_pos.le
  calc lam t = r * max 0 (1 + t / δ) := rfl
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left (max_le zero_le_one (by linarith)) r_pos.le
    _ = r := mul_one r

private theorem xt_continuous_lam : Continuous lam := by
  unfold lam
  fun_prop

private theorem continuous_ψfun : Continuous ψfun := by
  have hg : ContinuousOn (fun x : X => φ.symm (c₀ + lam x.1.2 • dir x.1.1))
      {x : X | x.1.2 ≤ 0} := by
    intro x hx
    have hx : x.1.2 ≤ 0 := hx
    have h2 : x.1.2 ^ 2 = f x.1.1 := x.2
    refine ContinuousAt.continuousWithinAt ?_
    rcases lt_or_ge x.1.2 (-δ) with hlt | hge
    · -- below `-δ` the map is constant, equal to `qp`
      refine Filter.EventuallyEq.continuousAt (y := φ.symm c₀) ?_
      have hopen : IsOpen {y : X | y.1.2 < -δ} := isOpen_lt (by fun_prop) continuous_const
      filter_upwards [hopen.mem_nhds hlt] with y hy
      rw [xt_lam_eq_zero (le_of_lt hy), zero_smul, add_zero]
    · -- in the collar `-δ ≤ t ≤ 0` the point lies in the chart, away from `c₀`
      have hsq : f x.1.1 < R - r := by
        rw [← h2]
        nlinarith [δ_sq_lt, δ_pos]
      obtain ⟨hs, hd⟩ := f_spec hsq
      have hne : φ x.1.1 ≠ c₀ := by
        intro h
        rw [h, dist_self] at hd
        nlinarith [r_pos, sq_nonneg x.1.2]
      have hmem : c₀ + lam x.1.2 • dir x.1.1 ∈ φ.target := by
        apply closedBall_r_subset_target
        rw [mem_closedBall, dist_eq_norm_sub, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (xt_lam_nonneg _)]
        calc lam x.1.2 * ‖dir x.1.1‖ ≤ r * 1 :=
              mul_le_mul (xt_lam_le hx) (xt_norm_dir_le _) (norm_nonneg _) r_pos.le
          _ = r := mul_one r
      have hdir : ContinuousAt dir x.1.1 := xt_continuousAt_dir hs hne
      have hlam := xt_continuous_lam
      have harg : ContinuousAt (fun y : X => c₀ + lam y.1.2 • dir y.1.1) x := by
        fun_prop
      exact (φ.continuousAt_symm hmem).comp_of_eq harg rfl
  have hfg : ∀ x : X, (0 : ℝ) = x.1.2 → x.1.1 = φ.symm (c₀ + lam x.1.2 • dir x.1.1) := by
    intro x hx
    have h2 : x.1.2 ^ 2 = f x.1.1 := x.2
    have h0 : f x.1.1 = 0 := by
      rw [← h2, ← hx]
      norm_num
    obtain ⟨hs, hd⟩ := f_spec (show f x.1.1 < R - r by rw [h0, R_sub_r]; exact r_pos)
    rw [h0, zero_add] at hd
    have hne : φ x.1.1 ≠ c₀ := by
      intro h
      rw [h, dist_self] at hd
      exact r_pos.ne hd
    rw [← hx, xt_lam_zero, ← hd, xt_add_dist_smul_dir hne, φ.left_inv hs]
  unfold ψfun
  exact continuous_if_le continuous_const (by fun_prop) (by fun_prop) hg hfg

/-- The collapse map as a continuous map. -/
private def ψ : C(X, Q) := ⟨ψfun, continuous_ψfun⟩

/-- The sheet swap. -/
private def τ : C(X, X) :=
  ⟨fun x => ⟨(x.1.1, -x.1.2), by change (-x.1.2) ^ 2 = _; rw [neg_sq]; exact x.2⟩, by fun_prop⟩

/-! ## The safe region and its two lifts to `X` -/

/-- The safe region as a space. -/
private abbrev KK : Type := K

private theorem one_mem_Zs : (1 : S3) ∈ Zs := Or.inr (Or.inl (by simp))

/-- The basepoint of the safe region. -/
private def q₀ : KK := ⟨proj 1, 1, one_mem_Zs, rfl⟩

private theorem f_nonneg_of_mem_K {q : Q} (hq : q ∈ K) : 0 ≤ f q := by
  rw [f_eq_of_mem_K hq]; unfold r; linarith [R_pos]

/-- The safe region on the upper sheet. -/
private def Φp : C(KK, X) :=
  ⟨fun q => ⟨(q.1, √(f q.1)), by
      change √(f q.1) ^ 2 = _; rw [Real.sq_sqrt (f_nonneg_of_mem_K q.2)]⟩,
    by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.prodMk
        (Real.continuous_sqrt.comp (continuous_f.comp continuous_subtype_val))⟩

/-- The safe region on the lower sheet. -/
private def Φn : C(KK, X) :=
  ⟨fun q => ⟨(q.1, -√(f q.1)), by
      change (-√(f q.1)) ^ 2 = _; rw [neg_sq, Real.sq_sqrt (f_nonneg_of_mem_K q.2)]⟩,
    by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.prodMk
        (Real.continuous_sqrt.comp (continuous_f.comp continuous_subtype_val)).neg⟩

/-- The inclusion of the safe region. -/
private def inclK : C(KK, Q) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The basepoint of `X`. -/
private abbrev x₀ : X := Φp q₀

private instance : Nonempty X := ⟨x₀⟩

/-! ## The two generating loops -/

/-- Quarter circle from `1` to `i`. -/
private def αℍ (t : ℝ) : ℍ[ℝ] := ⟨Real.cos (Real.pi / 2 * t), Real.sin (Real.pi / 2 * t), 0, 0⟩
/-- Quarter circle from `1` to `j`. -/
private def βℍ (t : ℝ) : ℍ[ℝ] := ⟨Real.cos (Real.pi / 2 * t), 0, Real.sin (Real.pi / 2 * t), 0⟩

/-- A quaternion whose coordinates have square sum one has norm one. -/
private theorem l1_norm_eq_one {q : ℍ[ℝ]} (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) :
    ‖q‖ = 1 := by
  have h2 : ‖q‖ * ‖q‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    exact h
  nlinarith [norm_nonneg q]

private theorem norm_αℍ (t : ℝ) : ‖αℍ t‖ = 1 := l1_norm_eq_one (by simp [αℍ])
private theorem norm_βℍ (t : ℝ) : ‖βℍ t‖ = 1 := l1_norm_eq_one (by simp [βℍ])

/-- `αℍ` as a unit quaternion. -/
private def αS (t : ℝ) : S3 := mkS3 (αℍ t) (norm_αℍ t)
/-- `βℍ` as a unit quaternion. -/
private def βS (t : ℝ) : S3 := mkS3 (βℍ t) (norm_βℍ t)

private theorem αS_mem_Zs (t : ℝ) : αS t ∈ Zs := Or.inr (Or.inr (Or.inl rfl))
private theorem βS_mem_Zs (t : ℝ) : βS t ∈ Zs := Or.inr (Or.inl rfl)

/-- A map into the quaternions is continuous if its four coordinates are. -/
private theorem l1_continuous_quat {Y : Type*} [TopologicalSpace Y] {a b c d : Y → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous fun y => (⟨a y, b y, c y, d y⟩ : ℍ[ℝ]) := by
  have h : (fun y => (⟨a y, b y, c y, d y⟩ : ℍ[ℝ])) = fun y =>
      a y • (1 : ℍ[ℝ]) + b y • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) + c y • (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) +
        d y • (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) := by
    funext y
    ext <;> simp
  rw [h]
  fun_prop

private theorem l1_continuous_αS : Continuous αS := by
  unfold αS mkS3 αℍ
  exact (l1_continuous_quat (by fun_prop) (by fun_prop) continuous_const
    continuous_const).subtype_mk _

private theorem l1_continuous_βS : Continuous βS := by
  unfold βS mkS3 βℍ
  exact (l1_continuous_quat (by fun_prop) continuous_const (by fun_prop)
    continuous_const).subtype_mk _

/-- A unit quaternion with integer coordinates lies in `Q₈`. -/
private theorem l1_mem_Q8 {v : S3} (a b c d : ℤ) (ha : (v : ℍ[ℝ]).re = a) (hb : (v : ℍ[ℝ]).imI = b)
    (hc : (v : ℍ[ℝ]).imJ = c) (hd : (v : ℍ[ℝ]).imK = d) : v ∈ Q8 :=
  ⟨⟨a, ha.symm⟩, ⟨b, hb.symm⟩, ⟨c, hc.symm⟩, ⟨d, hd.symm⟩⟩

/-- Elements of `Q₈` project to the basepoint. -/
private theorem l1_proj_eq_one {v : S3} (hv : v ∈ Q8) : proj v = proj 1 := by
  have h := QuotientGroup.mk_mul_of_mem (1 : S3) hv
  rwa [one_mul] at h

private theorem l1_eI_mem : eI ∈ Q8 :=
  l1_mem_Q8 0 1 0 0 (by simp [eI, mkS3]) (by simp [eI, mkS3]) (by simp [eI, mkS3])
    (by simp [eI, mkS3])

private theorem l1_eJ_mem : eJ ∈ Q8 :=
  l1_mem_Q8 0 0 1 0 (by simp [eJ, mkS3]) (by simp [eJ, mkS3]) (by simp [eJ, mkS3])
    (by simp [eJ, mkS3])

private theorem l1_αS_zero : αS 0 = 1 := by
  apply Subtype.ext
  change αℍ 0 = 1
  ext <;> simp [αℍ]

private theorem l1_βS_zero : βS 0 = 1 := by
  apply Subtype.ext
  change βℍ 0 = 1
  ext <;> simp [βℍ]

private theorem l1_αS_one_mem : αS 1 ∈ Q8 :=
  l1_mem_Q8 0 1 0 0 (by simp [αS, mkS3, αℍ]) (by simp [αS, mkS3, αℍ]) (by simp [αS, mkS3, αℍ])
    (by simp [αS, mkS3, αℍ])

private theorem l1_βS_one_mem : βS 1 ∈ Q8 :=
  l1_mem_Q8 0 0 1 0 (by simp [βS, mkS3, βℍ]) (by simp [βS, mkS3, βℍ]) (by simp [βS, mkS3, βℍ])
    (by simp [βS, mkS3, βℍ])

/-- The loop `a` (image of the quarter circle from `1` to `i`). -/
private def loopA : Path q₀ q₀ where
  toFun t := ⟨proj (αS t), αS t, αS_mem_Zs t, rfl⟩
  continuous_toFun :=
    (QuotientGroup.continuous_mk.comp (l1_continuous_αS.comp continuous_subtype_val)).subtype_mk _
  source' := by
    apply Subtype.ext
    change proj (αS ((0 : unitInterval) : ℝ)) = proj 1
    rw [Set.Icc.coe_zero, l1_αS_zero]
  target' := by
    apply Subtype.ext
    change proj (αS ((1 : unitInterval) : ℝ)) = proj 1
    rw [Set.Icc.coe_one]
    exact l1_proj_eq_one l1_αS_one_mem

/-- The loop `b` (image of the quarter circle from `1` to `j`). -/
private def loopB : Path q₀ q₀ where
  toFun t := ⟨proj (βS t), βS t, βS_mem_Zs t, rfl⟩
  continuous_toFun :=
    (QuotientGroup.continuous_mk.comp (l1_continuous_βS.comp continuous_subtype_val)).subtype_mk _
  source' := by
    apply Subtype.ext
    change proj (βS ((0 : unitInterval) : ℝ)) = proj 1
    rw [Set.Icc.coe_zero, l1_βS_zero]
  target' := by
    apply Subtype.ext
    change proj (βS ((1 : unitInterval) : ℝ)) = proj 1
    rw [Set.Icc.coe_one]
    exact l1_proj_eq_one l1_βS_one_mem

/-- The class of `loopA`. -/
private def a' : FundamentalGroup KK q₀ :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopA)
/-- The class of `loopB`. -/
private def b' : FundamentalGroup KK q₀ :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopB)

/-! ### The relation `a² = b²` -/

/-- The half great circle `cos (π t) + sin (π t) (cos (π s / 2) i + sin (π s / 2) j)`. -/
private def l1_Hℍ (s t : ℝ) : ℍ[ℝ] :=
  ⟨Real.cos (Real.pi * t), Real.sin (Real.pi * t) * Real.cos (Real.pi / 2 * s),
    Real.sin (Real.pi * t) * Real.sin (Real.pi / 2 * s), 0⟩

private theorem l1_norm_Hℍ (s t : ℝ) : ‖l1_Hℍ s t‖ = 1 := by
  apply l1_norm_eq_one
  have h1 := Real.cos_sq_add_sin_sq (Real.pi * t)
  have h2 := Real.cos_sq_add_sin_sq (Real.pi / 2 * s)
  dsimp only [l1_Hℍ]
  linear_combination Real.sin (Real.pi * t) ^ 2 * h2 + h1

/-- `l1_Hℍ` as a unit quaternion. -/
private def l1_HS (s t : ℝ) : S3 := mkS3 (l1_Hℍ s t) (l1_norm_Hℍ s t)

private theorem l1_HS_mem_Zs (s t : ℝ) : l1_HS s t ∈ Zs := Or.inr (Or.inr (Or.inr rfl))

private theorem l1_continuous_HS : Continuous fun p : ℝ × ℝ => l1_HS p.1 p.2 := by
  unfold l1_HS mkS3 l1_Hℍ
  exact (l1_continuous_quat (by fun_prop) (by fun_prop) (by fun_prop)
    continuous_const).subtype_mk _

/-- The point of the safe region given by `l1_HS s t`. -/
private def l1_Hk (s t : ℝ) : KK := ⟨proj (l1_HS s t), l1_HS s t, l1_HS_mem_Zs s t, rfl⟩

private theorem l1_Hk_zero (s : ℝ) : l1_Hk s 0 = q₀ := by
  apply Subtype.ext
  change proj (l1_HS s 0) = proj 1
  congr 1
  apply Subtype.ext
  change l1_Hℍ s 0 = 1
  ext <;> simp [l1_Hℍ]

private theorem l1_Hk_one (s : ℝ) : l1_Hk s 1 = q₀ := by
  apply Subtype.ext
  change proj (l1_HS s 1) = proj 1
  exact l1_proj_eq_one (l1_mem_Q8 (-1) 0 0 0 (by simp [l1_HS, mkS3, l1_Hℍ])
    (by simp [l1_HS, mkS3, l1_Hℍ]) (by simp [l1_HS, mkS3, l1_Hℍ]) (by simp [l1_HS, mkS3, l1_Hℍ]))

/-- The loop `t ↦ l1_Hk s t`. -/
private def l1_P (s : ℝ) : Path q₀ q₀ where
  toFun t := l1_Hk s t
  continuous_toFun :=
    (QuotientGroup.continuous_mk.comp (l1_continuous_HS.comp
      (continuous_const.prodMk continuous_subtype_val))).subtype_mk _
  source' := by
    show l1_Hk s ((0 : unitInterval) : ℝ) = q₀
    rw [Set.Icc.coe_zero, l1_Hk_zero]
  target' := by
    show l1_Hk s ((1 : unitInterval) : ℝ) = q₀
    rw [Set.Icc.coe_one, l1_Hk_one]

/-- A homotopy from `l1_P 0` to `l1_P 1`. -/
private def l1_homotopy : Path.Homotopy (l1_P 0) (l1_P 1) where
  toFun x := l1_Hk x.1 x.2
  continuous_toFun :=
    (QuotientGroup.continuous_mk.comp (l1_continuous_HS.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
  map_zero_left t := by
    change l1_Hk ((0 : unitInterval) : ℝ) t = l1_Hk 0 t
    rw [Set.Icc.coe_zero]
  map_one_left t := by
    change l1_Hk ((1 : unitInterval) : ℝ) t = l1_Hk 1 t
    rw [Set.Icc.coe_one]
  prop' s t ht := by
    change l1_Hk s t = l1_Hk 0 t
    rcases ht with rfl | rfl
    · rw [Set.Icc.coe_zero, l1_Hk_zero, l1_Hk_zero]
    · rw [Set.Icc.coe_one, l1_Hk_one, l1_Hk_one]

private theorem l1_αS_two_mul (t : ℝ) : αS (2 * t) = l1_HS 0 t := by
  apply Subtype.ext
  change αℍ (2 * t) = l1_Hℍ 0 t
  have h : Real.pi / 2 * (2 * t) = Real.pi * t := by ring
  ext <;> simp [αℍ, l1_Hℍ, h]

private theorem l1_βS_two_mul (t : ℝ) : βS (2 * t) = l1_HS 1 t := by
  apply Subtype.ext
  change βℍ (2 * t) = l1_Hℍ 1 t
  have h : Real.pi / 2 * (2 * t) = Real.pi * t := by ring
  ext <;> simp [βℍ, l1_Hℍ, h]

private theorem l1_αS_sub_mul (t : ℝ) : αS (2 * t - 1) * eI = l1_HS 0 t := by
  apply Subtype.ext
  change αℍ (2 * t - 1) * ⟨0, 1, 0, 0⟩ = l1_Hℍ 0 t
  have h : Real.pi / 2 * (2 * t - 1) = Real.pi * t - Real.pi / 2 := by ring
  ext <;> simp [αℍ, l1_Hℍ, h, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]

private theorem l1_βS_sub_mul (t : ℝ) : βS (2 * t - 1) * eJ = l1_HS 1 t := by
  apply Subtype.ext
  change βℍ (2 * t - 1) * ⟨0, 0, 1, 0⟩ = l1_Hℍ 1 t
  have h : Real.pi / 2 * (2 * t - 1) = Real.pi * t - Real.pi / 2 := by ring
  ext <;> simp [βℍ, l1_Hℍ, h, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]

private theorem l1_trans_A : loopA.trans loopA = l1_P 0 := by
  refine Path.ext (funext fun t => ?_)
  rw [Path.trans_apply]
  split_ifs with h
  · apply Subtype.ext
    change proj (αS (2 * (t : ℝ))) = proj (l1_HS 0 t)
    rw [l1_αS_two_mul]
  · apply Subtype.ext
    change proj (αS (2 * (t : ℝ) - 1)) = proj (l1_HS 0 t)
    rw [← l1_αS_sub_mul]
    exact (QuotientGroup.mk_mul_of_mem _ l1_eI_mem).symm

private theorem l1_trans_B : loopB.trans loopB = l1_P 1 := by
  refine Path.ext (funext fun t => ?_)
  rw [Path.trans_apply]
  split_ifs with h
  · apply Subtype.ext
    change proj (βS (2 * (t : ℝ))) = proj (l1_HS 1 t)
    rw [l1_βS_two_mul]
  · apply Subtype.ext
    change proj (βS (2 * (t : ℝ) - 1)) = proj (l1_HS 1 t)
    rw [← l1_βS_sub_mul]
    exact (QuotientGroup.mk_mul_of_mem _ l1_eJ_mem).symm

/-! ## The quaternion relations between `a'` and `b'` -/

/-- The first quaternion relation `a'² = b'²`. -/
private theorem rel1 : a' * a' = b' * b' := by
  have h : Path.Homotopic.Quotient.mk (loopA.trans loopA) =
      Path.Homotopic.Quotient.mk (loopB.trans loopB) := by
    rw [l1_trans_A, l1_trans_B]
    exact Path.Homotopic.Quotient.eq.mpr ⟨l1_homotopy⟩
  exact congrArg FundamentalGroup.fromPath h

/-! ### The relation `b' * a' = a'⁻¹ * b'`

Both `loopA.trans loopB` and `loopB.trans loopA.symm` lift to paths from `1` to `-k` in the
region `l2_C` of nonzero quaternions with nonnegative real part and a vanishing `i`- or
`j`-coordinate. This region is star-convex about `1`, hence simply connected, so the two lifts are
homotopic; the normalisation map `l2_N : l2_C → KK` carries this homotopy down. -/

/-- Nonzero quaternions with nonnegative real part and a vanishing `i`- or `j`-coordinate. -/
private def l2_C : Set ℍ[ℝ] := {w | w ≠ 0 ∧ 0 ≤ w.re ∧ (w.imI = 0 ∨ w.imJ = 0)}

private theorem l2_one_mem : (1 : ℍ[ℝ]) ∈ l2_C := ⟨one_ne_zero, by simp, Or.inl (by simp)⟩

private theorem l2_starConvex : StarConvex ℝ (1 : ℍ[ℝ]) l2_C := by
  rintro w ⟨hw0, hre, hij⟩ a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    rw [zero_smul, one_smul, zero_add]
    exact ⟨hw0, hre, hij⟩
  · have hre' : 0 < (a • (1 : ℍ[ℝ]) + b • w).re := by
      simp only [re_add, re_smul, re_one, smul_eq_mul, mul_one]
      nlinarith [mul_nonneg hb hre]
    refine ⟨fun h => by simp [h] at hre', hre'.le, ?_⟩
    rcases hij with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])

private instance l2_simplyConnected : SimplyConnectedSpace l2_C := by
  have := l2_starConvex.contractibleSpace ⟨1, l2_one_mem⟩
  infer_instance

private theorem l2_ne_zero {w : ℍ[ℝ]} (h : ‖w‖ = 1) : w ≠ 0 := by
  rintro rfl
  simp at h

/-- Normalisation of a point of `l2_C` to a unit quaternion. -/
private def l2_unit (w : l2_C) : S3 :=
  mkS3 (‖(w : ℍ[ℝ])‖⁻¹ • (w : ℍ[ℝ])) (norm_smul_inv_norm w.2.1)

private theorem l2_unit_mem (w : l2_C) : l2_unit w ∈ Zs := by
  rcases w.2.2.2 with h | h
  · exact Or.inr (Or.inl (by simp [l2_unit, mkS3, h]))
  · exact Or.inr (Or.inr (Or.inl (by simp [l2_unit, mkS3, h])))

private theorem l2_continuous_unit : Continuous l2_unit :=
  ((continuous_subtype_val.norm.inv₀ fun w => norm_ne_zero_iff.mpr w.2.1).smul
    continuous_subtype_val).subtype_mk _

/-- The normalisation map from `l2_C` to the safe region. -/
private def l2_N : C(l2_C, KK) where
  toFun w := ⟨proj (l2_unit w), l2_unit w, l2_unit_mem w, rfl⟩
  continuous_toFun := (QuotientGroup.continuous_mk.comp l2_continuous_unit).subtype_mk _

/-- If a point of `l2_C` is `v * g` with `v` a unit quaternion and `g ∈ Q₈`, then its image
under the normalisation map is the class of `v`. -/
private theorem l2_N_eq (w : l2_C) (v g : S3) (hg : g ∈ Q8) (hw : (w : ℍ[ℝ]) = v * g) :
    (l2_N w : Q) = proj v := by
  have hn : ‖(w : ℍ[ℝ])‖ = 1 := by
    rw [hw, norm_mul, norm_eq_of_mem_sphere, norm_eq_of_mem_sphere, one_mul]
  have hu : l2_unit w = v * g := by
    apply Subtype.ext
    change ‖(w : ℍ[ℝ])‖⁻¹ • (w : ℍ[ℝ]) = ((v * g : S3) : ℍ[ℝ])
    rw [hn, inv_one, one_smul, hw]
    rfl
  change proj (l2_unit w) = proj v
  rw [hu]
  exact QuotientGroup.mk_mul_of_mem v hg

/-- A path in `l2_C` given by a continuous function on `ℝ`. -/
private def l2_path (f : ℝ → ℍ[ℝ]) (hf : Continuous f) (hC : ∀ t : unitInterval, f t ∈ l2_C)
    {x y : l2_C} (h0 : f 0 = x) (h1 : f 1 = y) : Path x y where
  toFun t := ⟨f t, hC t⟩
  continuous_toFun := (hf.comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext h0
  target' := Subtype.ext h1

private theorem l2_continuous_αℍ : Continuous αℍ := by
  have h : αℍ = fun t => (Real.cos (Real.pi / 2 * t) : ℍ[ℝ]) +
      Real.sin (Real.pi / 2 * t) • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by
    funext t
    ext <;> simp [αℍ]
  rw [h]
  exact (Quaternion.continuous_coe.comp (Real.continuous_cos.comp
    (continuous_const.mul continuous_id))).add
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).smul continuous_const)

private theorem l2_continuous_βℍ : Continuous βℍ := by
  have h : βℍ = fun t => (Real.cos (Real.pi / 2 * t) : ℍ[ℝ]) +
      Real.sin (Real.pi / 2 * t) • (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) := by
    funext t
    ext <;> simp [βℍ]
  rw [h]
  exact (Quaternion.continuous_coe.comp (Real.continuous_cos.comp
    (continuous_const.mul continuous_id))).add
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).smul continuous_const)

private theorem l2_cos_nonneg (t : unitInterval) : 0 ≤ Real.cos (Real.pi / 2 * t) := by
  have h0 := unitInterval.nonneg t
  have h1 := unitInterval.le_one t
  have hpi := Real.pi_pos
  exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩

private theorem l2_norm_nk : ‖(⟨0, 0, 0, -1⟩ : ℍ[ℝ])‖ = 1 := by
  rw [show (⟨0, 0, 0, -1⟩ : ℍ[ℝ]) = -⟨0, 0, 0, 1⟩ by ext <;> simp, norm_neg, norm_eK]

/-- The unit quaternion `-k`. -/
private def l2_nk : S3 := mkS3 ⟨0, 0, 0, -1⟩ l2_norm_nk

private theorem l2_nk_mem : l2_nk ∈ Q8 :=
  ⟨⟨0, by simp [l2_nk, mkS3]⟩, ⟨0, by simp [l2_nk, mkS3]⟩, ⟨0, by simp [l2_nk, mkS3]⟩,
    ⟨-1, by simp [l2_nk, mkS3]⟩⟩

/-- The point `1` of `l2_C`. -/
private def l2_c1 : l2_C := ⟨1, l2_one_mem⟩
/-- The point `i` of `l2_C`. -/
private def l2_ci : l2_C := ⟨⟨0, 1, 0, 0⟩, l2_ne_zero norm_eI, le_rfl, Or.inr rfl⟩
/-- The point `j` of `l2_C`. -/
private def l2_cj : l2_C := ⟨⟨0, 0, 1, 0⟩, l2_ne_zero norm_eJ, le_rfl, Or.inl rfl⟩
/-- The point `-k` of `l2_C`. -/
private def l2_cnk : l2_C := ⟨⟨0, 0, 0, -1⟩, l2_ne_zero l2_norm_nk, le_rfl, Or.inl rfl⟩

private theorem l2_A_mem (t : unitInterval) : αℍ t ∈ l2_C :=
  ⟨l2_ne_zero (norm_αℍ t), l2_cos_nonneg t, Or.inr rfl⟩

/-- The quarter circle `t ↦ βℍ t * i` from `i` to `-k`. -/
private def l2_fBi (t : ℝ) : ℍ[ℝ] := βℍ t * ⟨0, 1, 0, 0⟩

private theorem l2_Bi_mem (t : unitInterval) : l2_fBi t ∈ l2_C := by
  refine ⟨l2_ne_zero (by rw [l2_fBi, norm_mul, norm_βℍ, norm_eI, one_mul]), ?_, Or.inr ?_⟩
  · simp [l2_fBi, βℍ]
  · simp [l2_fBi, βℍ]

private theorem l2_B_mem (t : unitInterval) : βℍ t ∈ l2_C :=
  ⟨l2_ne_zero (norm_βℍ t), l2_cos_nonneg t, Or.inl rfl⟩

/-- The path `t ↦ αℍ (1 - t) * (-k)` from `j` to `-k`. -/
private def l2_fAk (t : ℝ) : ℍ[ℝ] := αℍ (1 - t) * ⟨0, 0, 0, -1⟩

private theorem l2_Ak_mem (t : unitInterval) : l2_fAk t ∈ l2_C := by
  refine ⟨l2_ne_zero (by rw [l2_fAk, norm_mul, norm_αℍ, l2_norm_nk, one_mul]), ?_, Or.inl ?_⟩
  · simp [l2_fAk, αℍ]
  · simp [l2_fAk, αℍ]

/-- Lift of `loopA`: the quarter circle from `1` to `i`. -/
private def l2_A : Path l2_c1 l2_ci :=
  l2_path αℍ l2_continuous_αℍ l2_A_mem (by ext <;> simp [αℍ, l2_c1])
    (by ext <;> simp [αℍ, l2_ci])

/-- Lift of `loopB` starting at `i`: the quarter circle `t ↦ βℍ t * i` from `i` to `-k`. -/
private def l2_Bi : Path l2_ci l2_cnk :=
  l2_path l2_fBi (l2_continuous_βℍ.mul continuous_const) l2_Bi_mem
    (by ext <;> simp [l2_fBi, βℍ, l2_ci]) (by ext <;> simp [l2_fBi, βℍ, l2_cnk])

/-- Lift of `loopB`: the quarter circle from `1` to `j`. -/
private def l2_B : Path l2_c1 l2_cj :=
  l2_path βℍ l2_continuous_βℍ l2_B_mem (by ext <;> simp [βℍ, l2_c1])
    (by ext <;> simp [βℍ, l2_cj])

/-- Lift of `loopA.symm` starting at `j`: `t ↦ αℍ (1 - t) * (-k)` from `j` to `-k`. -/
private def l2_Ak : Path l2_cj l2_cnk :=
  l2_path l2_fAk
    ((l2_continuous_αℍ.comp (continuous_const.sub continuous_id)).mul continuous_const)
    l2_Ak_mem (by ext <;> simp [l2_fAk, αℍ, l2_cj]) (by ext <;> simp [l2_fAk, αℍ, l2_cnk])

private theorem l2_src : q₀ = l2_N l2_c1 :=
  Subtype.ext (l2_N_eq l2_c1 1 1 Q8.one_mem (mul_one _).symm).symm

private theorem l2_tgt : q₀ = l2_N l2_cnk :=
  Subtype.ext (l2_N_eq l2_cnk 1 l2_nk l2_nk_mem (one_mul _).symm).symm

private theorem l2_A_eq (t : unitInterval) : loopA t = l2_N (l2_A t) := by
  apply Subtype.ext
  rw [l2_N_eq (l2_A t) (αS t) 1 Q8.one_mem (by change αℍ t = αℍ t * 1; rw [mul_one])]
  rfl

private theorem l2_Bi_eq (t : unitInterval) : loopB t = l2_N (l2_Bi t) := by
  apply Subtype.ext
  rw [l2_N_eq (l2_Bi t) (βS t) eI l1_eI_mem rfl]
  rfl

private theorem l2_B_eq (t : unitInterval) : loopB t = l2_N (l2_B t) := by
  apply Subtype.ext
  rw [l2_N_eq (l2_B t) (βS t) 1 Q8.one_mem (by change βℍ t = βℍ t * 1; rw [mul_one])]
  rfl

private theorem l2_Ak_eq (t : unitInterval) : loopA.symm t = l2_N (l2_Ak t) := by
  apply Subtype.ext
  rw [l2_N_eq (l2_Ak t) (αS (1 - t)) l2_nk l2_nk_mem rfl]
  rfl

private theorem l2_trans_eq {x y z : KK} {x' y' z' : l2_C} (γ₁ : Path x y) (γ₂ : Path y z)
    (p₁ : Path x' y') (p₂ : Path y' z') (h₁ : ∀ t, γ₁ t = l2_N (p₁ t))
    (h₂ : ∀ t, γ₂ t = l2_N (p₂ t)) (t : unitInterval) :
    (γ₁.trans γ₂) t = l2_N ((p₁.trans p₂) t) := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact h₁ _
  · exact h₂ _

private theorem l2_homotopic : (loopA.trans loopB).Homotopic (loopB.trans loopA.symm) := by
  have e₁ : loopA.trans loopB =
      ((l2_A.trans l2_Bi).map l2_N.continuous).cast l2_src l2_tgt := by
    refine Path.ext (funext fun t => ?_)
    exact l2_trans_eq loopA loopB l2_A l2_Bi l2_A_eq l2_Bi_eq t
  have e₂ : loopB.trans loopA.symm =
      ((l2_B.trans l2_Ak).map l2_N.continuous).cast l2_src l2_tgt := by
    refine Path.ext (funext fun t => ?_)
    exact l2_trans_eq loopB loopA.symm l2_B l2_Ak l2_B_eq l2_Ak_eq t
  rw [e₁, e₂]
  exact ((SimplyConnectedSpace.paths_homotopic (l2_A.trans l2_Bi) (l2_B.trans l2_Ak)).map
    l2_N).pathCast l2_src l2_tgt

/-- The second quaternion relation `b' a' = a'⁻¹ b'`. -/
private theorem rel2 : b' * a' = a'⁻¹ * b' := by
  change FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopA.trans loopB)) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopB.trans loopA.symm))
  rw [Path.Homotopic.Quotient.eq.mpr l2_homotopic]

/-! ## The monodromy of `a'²` is nontrivial -/

private theorem q_αS_one : αS 1 = eI := by
  apply Subtype.ext
  change αℍ 1 = ⟨0, 1, 0, 0⟩
  ext <;> simp [αℍ]

/-- The element `i` of `Q₈`, acting on `S³` by right multiplication. -/
private def q_gI : Q8.op := ⟨MulOpposite.op eI, Subgroup.mem_op.mpr l1_eI_mem⟩

/-- The point `1` in the fibre of `proj` over the basepoint. -/
private def q_e : proj ⁻¹' {inclK q₀} := ⟨1, rfl⟩

/-- The lift of `loopA` to `S³` starting at `1`. -/
private def q_liftA : C(unitInterval, S3) :=
  ⟨fun t => αS t, l1_continuous_αS.comp continuous_subtype_val⟩

/-- The monodromy of the image of `a'` is right multiplication by `i`. -/
private theorem q_mono_a :
    isQCM.fundamentalGroupToMulOpposite q_e (FundamentalGroup.map inclK q₀ a') =
      MulOpposite.op q_gI := by
  have h : FundamentalGroup.map inclK q₀ a' =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopA.map inclK.continuous)) := rfl
  rw [h]
  refine isQCM.fundamentalGroupToMulOpposite_apply_mk_eq (Γ := q_liftA) ?_ ?_ ?_
  · funext t; rfl
  · change αS ((0 : unitInterval) : ℝ) = 1
    rw [Set.Icc.coe_zero]; exact l1_αS_zero
  · change αS ((1 : unitInterval) : ℝ) = 1 * eI
    rw [Set.Icc.coe_one, one_mul]; exact q_αS_one

/-- The loop `a'²` stays nontrivial in `S³/Q₈`: its monodromy is right multiplication by `-1`. -/
private theorem mono_ne : FundamentalGroup.map inclK q₀ (a' * a') ≠ 1 := by
  intro h
  have h1 := congrArg (isQCM.fundamentalGroupToMulOpposite q_e) h
  rw [map_mul, map_mul, q_mono_a, map_one, ← MulOpposite.op_mul, MulOpposite.op_eq_one_iff] at h1
  have h2 := congrArg (fun g : Q8.op => (((g : S3ᵐᵒᵖ).unop : S3) : ℍ[ℝ]).re) h1
  norm_num [q_gI, eI, mkS3] at h2

/-- The collapse map is the identity on the upper copy of the safe region. -/
private theorem ψ_comp_Φp : ψ.comp Φp = inclK := by
  ext q
  change ψfun (Φp q) = q.1
  unfold ψfun
  exact ite_eq_left (Real.sqrt_nonneg _)

/-- The collapse map sends the lower copy of the safe region to `qp`. -/
private theorem ψ_comp_Φn : ψ.comp Φn = ContinuousMap.const KK qp := by
  ext q
  change ψfun (Φn q) = qp
  have hδ : δ ≤ √(f q.1) := by
    rw [f_eq_of_mem_K q.2]
    exact (Real.le_sqrt' δ_pos).mpr δ_sq_lt.le
  have h2 : (Φn q).1.2 = -√(f q.1) := rfl
  unfold ψfun
  rw [ite_eq_right (not_le.mpr (by rw [h2]; linarith [δ_pos])), h2,
    xt_lam_eq_zero (by linarith), zero_smul, add_zero, φ_symm_c₀]

/-- After the sheet swap, the collapse map is the identity on the lower copy of the safe region. -/
private theorem ψτ_comp_Φn : (ψ.comp τ).comp Φn = inclK := by
  ext q
  change ψfun (τ (Φn q)) = q.1
  unfold ψfun
  exact ite_eq_left (show (0 : ℝ) ≤ -(-√(f q.1)) by rw [neg_neg]; exact Real.sqrt_nonneg _)

/-! ## Quaternion relations in `GL(4, ℝ)` -/

/-- Four vectors carrying the multiplication table of the quaternion units `1, i, j, k`
(with `A = i` and `B = j` acting on the left) are linearly independent: applying
`x - y A - z B - t A B` to a relation `x u0 + y u1 + z u2 + t u3 = 0` gives
`(x² + y² + z² + t²) u0 = 0`. -/
private theorem gl_linearIndependent {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A B : V →ₗ[ℝ] V) (u0 u1 u2 u3 : V) (h0 : u0 ≠ 0)
    (hA0 : A u0 = u1) (hA1 : A u1 = -u0) (hA2 : A u2 = u3) (hA3 : A u3 = -u2)
    (hB0 : B u0 = u2) (hB1 : B u1 = -u3) (hB2 : B u2 = -u0) (hB3 : B u3 = u1) :
    LinearIndependent ℝ ![u0, u1, u2, u3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_four, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
  have hA := congrArg A hg
  simp only [map_add, map_smul, map_zero, hA0, hA1, hA2, hA3] at hA
  have hB := congrArg B hg
  simp only [map_add, map_smul, map_zero, hB0, hB1, hB2, hB3] at hB
  have hAB := congrArg A hB
  simp only [map_add, map_smul, map_zero, map_neg, hA0, hA1, hA2, hA3] at hAB
  have key : (g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 + g 3 ^ 2) • u0 = 0 := by
    linear_combination (norm := module) g 0 • hg - g 1 • hA - g 2 • hB - g 3 • hAB
  have hsum : g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 + g 3 ^ 2 = 0 :=
    (smul_eq_zero.mp key).resolve_right h0
  have s0 := sq_nonneg (g 0)
  have s1 := sq_nonneg (g 1)
  have s2 := sq_nonneg (g 2)
  have s3 := sq_nonneg (g 3)
  have z0 : g 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have z1 : g 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have z2 : g 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have z3 : g 3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  intro i
  fin_cases i
  exacts [z0, z1, z2, z3]

/-- If `a² = b²`, `b a = a⁻¹ b` and `a² ≠ 1`, every injective homomorphism to `GL(4, ℝ)` sends
`a²` to `-1`. -/
private theorem gl_lemma {G : Type*} [Group G] (ρ : G →* GL (Fin 4) ℝ) (hρ : Function.Injective ρ)
    (a b : G) (h1 : a * a = b * b) (h2 : b * a = a⁻¹ * b) (h3 : a * a ≠ 1) :
    ρ (a * a) = -1 := by
  -- Step 1: identities in the group: `a * a` is central of order two in `⟨a, b⟩`.
  have e1 : b * (a * a) = a⁻¹ * a⁻¹ * b :=
    calc b * (a * a) = (b * a) * a := (mul_assoc _ _ _).symm
      _ = (a⁻¹ * b) * a := by rw [h2]
      _ = a⁻¹ * (b * a) := mul_assoc _ _ _
      _ = a⁻¹ * (a⁻¹ * b) := by rw [h2]
      _ = a⁻¹ * a⁻¹ * b := (mul_assoc _ _ _).symm
  have e2 : b * (a * a) = a * a * b := by rw [h1]; group
  have e3 : a * a = a⁻¹ * a⁻¹ := mul_right_cancel (e2.symm.trans e1)
  have g1 : a * a * (a * a) = 1 :=
    calc a * a * (a * a) = a * a * (a⁻¹ * a⁻¹) := congrArg (a * a * ·) e3
      _ = 1 := by group
  have ainv : a⁻¹ = a * (a * a) :=
    inv_eq_of_mul_eq_one_right (by simpa [mul_assoc] using g1)
  have g3 : b * a = a * (b * (a * a)) := by rw [e2, h2, ainv]; group
  have g5 : b * a * b = a := by rw [h2, mul_assoc, ← h1]; group
  -- Step 2: the representation by endomorphisms of `ℝ⁴`, and a vector `w ≠ 0` in the
  -- `-1`-eigenspace of `σ (a * a)`.
  let σ : G →* Module.End ℝ (Fin 4 → ℝ) :=
    (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin 4)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp ρ)
  have hσ : ∀ x y (v : Fin 4 → ℝ), σ x (σ y v) = σ (x * y) v := by
    intro x y v; rw [map_mul, mul_apply_eq_comp]
  have hσ1 : ∀ v : Fin 4 → ℝ, σ 1 v = v := by
    intro v; rw [map_one, one_apply_eq_self]
  have hM : σ (a * a) ≠ 1 := by
    intro h
    apply h3
    apply hρ
    rw [map_one]
    apply Units.ext
    apply Matrix.toLinAlgEquiv'.injective
    rw [Units.val_one, map_one]
    exact h
  obtain ⟨v, hv⟩ : ∃ v, σ (a * a) v ≠ v := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hM (LinearMap.ext hcon)
  obtain ⟨w, hw0, hMw⟩ : ∃ w, w ≠ 0 ∧ σ (a * a) w = -w := by
    refine ⟨v - σ (a * a) v, sub_ne_zero.mpr (Ne.symm hv), ?_⟩
    rw [map_sub, hσ, g1, hσ1, neg_sub]
  -- Step 3: the quaternionic multiplication table on `w, A w, B w, A B w`.
  have hA1 : σ a (σ a w) = -w := by rw [hσ, hMw]
  have hA3 : σ a (σ a (σ b w)) = -(σ b w) := by
    rw [hσ a a, hσ (a * a) b, ← e2, ← hσ b (a * a), hMw, map_neg]
  have hB1 : σ b (σ a w) = -(σ a (σ b w)) := by
    rw [hσ b a, g3, ← hσ a (b * (a * a)), ← hσ b (a * a), hMw, map_neg, map_neg]
  have hB2 : σ b (σ b w) = -w := by rw [hσ, ← h1, hMw]
  have hB3 : σ b (σ a (σ b w)) = σ a w := by rw [hσ b a, hσ (b * a) b, g5]
  have hM1 : σ (a * a) (σ a w) = -(σ a w) := by
    rw [hσ (a * a) a, mul_assoc, ← hσ a (a * a), hMw, map_neg]
  have hM2 : σ (a * a) (σ b w) = -(σ b w) := by
    rw [hσ (a * a) b, ← e2, ← hσ b (a * a), hMw, map_neg]
  have hM3 : σ (a * a) (σ a (σ b w)) = -(σ a (σ b w)) := by
    rw [hσ (a * a) a, mul_assoc, ← hσ a (a * a), hM2, map_neg]
  -- Step 4: these four vectors form a basis of `ℝ⁴` on which `σ (a * a)` acts as `-1`.
  have hli : LinearIndependent ℝ ![w, σ a w, σ b w, σ a (σ b w)] :=
    gl_linearIndependent (σ a) (σ b) w (σ a w) (σ b w) (σ a (σ b w)) hw0 rfl hA1 rfl hA3
      rfl hB1 hB2 hB3
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hEnd : σ (a * a) = -1 := by
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i <;>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hMw, hM1, hM2,
        hM3, LinearMap.neg_apply, one_apply_eq_self]
  apply Units.ext
  apply Matrix.toLinAlgEquiv'.injective
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  exact hEnd

/-! ## Proof of the main theorem -/

private theorem pathConnX : PathConnectedSpace X := by
  have : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace E3 X
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

/-- Induced maps on fundamental groups compose. -/
private theorem map_map {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (a : A) (u : FundamentalGroup A a) :
    FundamentalGroup.map g (f a) (FundamentalGroup.map f a u) =
      FundamentalGroup.map (g.comp f) a u := by
  apply CategoryTheory.End.ext
  obtain ⟨P, hP⟩ := Path.Homotopic.Quotient.mk_surjective u.asHom
  change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map u.asHom f) g =
    Path.Homotopic.Quotient.map u.asHom (g.comp f)
  rw [← hP]
  rfl

/-- A constant map induces the trivial homomorphism. -/
private theorem map_const_eq_one {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (b : B) (a : A)
    (u : FundamentalGroup A a) : FundamentalGroup.map (ContinuousMap.const A b) a u = 1 := by
  apply CategoryTheory.End.ext
  obtain ⟨P, hP⟩ := Path.Homotopic.Quotient.mk_surjective u.asHom
  change Path.Homotopic.Quotient.map u.asHom (ContinuousMap.const A b) =
    Path.Homotopic.Quotient.mk (Path.refl b)
  rw [← hP, ← Path.Homotopic.Quotient.mk_map]
  congr 1

/-- A map equal to the inclusion of the safe region does not kill `a' * a'`. -/
private theorem map_ne_one_of_eq_inclK (F : C(KK, Q)) (hF : F = inclK) :
    FundamentalGroup.map F q₀ (a' * a') ≠ 1 := by
  subst hF
  exact mono_ne

/-- A map equal to a constant map kills everything. -/
private theorem map_eq_one_of_eq_const (F : C(KK, Q)) (hF : F = ContinuousMap.const KK qp)
    (u : FundamentalGroup KK q₀) : FundamentalGroup.map F q₀ u = 1 := by
  subst hF
  exact map_const_eq_one qp q₀ u

/-- The double is a closed 3-manifold whose fundamental group has no faithful representation in
`GL(4, ℝ)`. -/
private theorem exists_nonlinear : ∃ (M : Closed3Manifold) (x : M.carrier),
    ∀ f : FundamentalGroup M.carrier x →* GL (Fin 4) ℝ, ¬ Function.Injective f := by
  have := pathConnX
  refine ⟨⟨X⟩, x₀, fun ρ hρ => ?_⟩
  let c : Path (Φn q₀) x₀ := PathConnectedSpace.somePath _ _
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath c
  let a₁ : FundamentalGroup X x₀ := FundamentalGroup.map Φp q₀ a'
  let b₁ : FundamentalGroup X x₀ := FundamentalGroup.map Φp q₀ b'
  let a₂ : FundamentalGroup X x₀ := E (FundamentalGroup.map Φn q₀ a')
  let b₂ : FundamentalGroup X x₀ := E (FundamentalGroup.map Φn q₀ b')
  have r11 : a₁ * a₁ = b₁ * b₁ := by
    simp only [a₁, b₁]; rw [← map_mul, ← map_mul, rel1]
  have r12 : b₁ * a₁ = a₁⁻¹ * b₁ := by
    simp only [a₁, b₁]; rw [← map_mul, ← map_inv, ← map_mul, rel2]
  have r21 : a₂ * a₂ = b₂ * b₂ := by
    simp only [a₂, b₂]; rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, rel1]
  have r22 : b₂ * a₂ = a₂⁻¹ * b₂ := by
    simp only [a₂, b₂]
    rw [← map_mul, ← map_mul, ← map_inv, ← map_inv, ← map_mul, ← map_mul, rel2]
  have hsq1 : a₁ * a₁ = FundamentalGroup.map Φp q₀ (a' * a') := by
    simp only [a₁]; rw [← map_mul]
  have hsq2 : a₂ * a₂ = E (FundamentalGroup.map Φn q₀ (a' * a')) := by
    simp only [a₂]; rw [← map_mul, ← map_mul]
  have hψ1 : FundamentalGroup.map ψ x₀ (a₁ * a₁) ≠ 1 := by
    rw [hsq1]
    exact (map_map Φp ψ q₀ (a' * a')).trans_ne (map_ne_one_of_eq_inclK _ ψ_comp_Φp)
  have n1 : a₁ * a₁ ≠ 1 := fun h => hψ1 (by rw [h, map_one])
  have n2 : a₂ * a₂ ≠ 1 := by
    intro h
    rw [hsq2] at h
    have h' : FundamentalGroup.map Φn q₀ (a' * a') = 1 := E.injective (h.trans E.map_one.symm)
    have : FundamentalGroup.map (ψ.comp τ) (Φn q₀) (FundamentalGroup.map Φn q₀ (a' * a')) = 1 := by
      rw [h', map_one]
    exact map_ne_one_of_eq_inclK _ ψτ_comp_Φn ((map_map Φn (ψ.comp τ) q₀ (a' * a')).symm.trans this)
  have n3 : a₁ * a₁ ≠ a₂ * a₂ := by
    intro h
    apply hψ1
    rw [h, hsq2]
    change FundamentalGroup.map ψ x₀
      (FundamentalGroup.fundamentalGroupMulEquivOfPath c (FundamentalGroup.map Φn q₀ (a' * a'))) = 1
    rw [FundamentalGroup.map_fundamentalGroupMulEquivOfPath ψ c, map_map Φn ψ q₀ (a' * a'),
      map_eq_one_of_eq_const _ ψ_comp_Φn, map_one]
  have e1 := gl_lemma ρ hρ a₁ b₁ r11 r12 n1
  have e2 := gl_lemma ρ hρ a₂ b₂ r21 r22 n2
  exact n3 (hρ (e1.trans e2.symm))

end

end QuaternionicDouble

/- **A non-linear 3-manifold group** (Button, answering `[Kir97, Problem 3.33]`
negatively). There is a closed connected topological 3-manifold `M` and a
basepoint `x` such that the fundamental group `π₁(M, x)` admits no faithful
(injective) representation into `GL(4, ℝ)`. -/
set_option linter.dupNamespace false in
/-- **A closed 3-manifold group with no faithful representation in $GL_4(\mathbb{R})$.** There
is a closed connected topological 3-manifold $M$ with a point $x$ such that no group
homomorphism from the fundamental group $\pi_1(M, x)$ to $GL_4(\mathbb{R})$ is injective.

Source: J. O. Button, *A 3-manifold group which is not four dimensional linear*,
arXiv:1210.3068 (2012); J. Pure Appl. Algebra 218 (2014), 1604–1619. Button proves more: some
closed orientable graph 3-manifolds have fundamental groups that are subgroups of $GL_4(k)$ for
no field $k$. The double of the quaternionic space form $S^3/Q_8$ minus a ball is a different
witness; it gives the counterexample over $\mathbb{R}$, not Button's result for every field.
See the discussion of [Kir97, Problem 3.33] in the K3 problem list. Via
leanprover/lean-eval@38361be, problem `nonlinear_three_manifold_group`. -/
theorem nonlinear_three_manifold_group :
    ∃ (M : Closed3Manifold) (x : M.carrier),
      ∀ f : FundamentalGroup M.carrier x →* GL (Fin 4) ℝ, ¬ Function.Injective f :=
  QuaternionicDouble.exists_nonlinear

end Topology

end MathlibExt.Topology.NonlinearThreeManifoldGroupWanted
