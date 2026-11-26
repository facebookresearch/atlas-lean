/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/VonNeumannDoubleCommutant.lean` (leanprover/lean-eval):
the statement of `vonNeumann_doubleCommutant_tfae` and its documentation.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.VonNeumannDoubleCommutant` —
vonNeumann_doubleCommutant_tfae (manifest `manifests/problems/vonNeumann_doubleCommutant_tfae.toml`,
rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.VonNeumannDoubleCommutantWanted` namespace.
Mathematical statements are unchanged.
Source: J. von Neumann, Zur Algebra der Funktionaloperationen und Theorie
der normalen Operatoren, Math. Ann. 102 (1930), 370-427.

The present module moves the statement to the proved library and supplies its proof.
-/
module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.TFAE

/-!
# Von Neumann's double commutant theorem

For a unital *-subalgebra `S` of bounded operators on a complex Hilbert space `H`, the
following are equivalent:

1. `S` equals its double commutant `S''`.
2. `S` is closed in the weak operator topology.
3. `S` is closed in the strong operator topology (in Mathlib, the topology of pointwise
   convergence on continuous linear maps).

The WOT and SOT live on irreducible type copies of `H →L[ℂ] H`, so each closed-ness
condition is stated as the closedness of the image of `S` under the canonical inclusion
into the corresponding type copy.
-/

namespace MathlibExt.Analysis.VonNeumannDoubleCommutantWanted.Analysis

open Set ContinuousLinearMapWOT
open scoped Topology ComplexInnerProductSpace

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Amplification

variable {ι : Type*}
local notation "K" => PiLp 2 (fun _ : ι => H)

/-- The diagonal action of an operator on a finite Hilbert sum. -/
private noncomputable def diagonal (A : H →L[ℂ] H) : K →L[ℂ] K :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  e.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.piMap fun _ : ι => A).comp
    e.toContinuousLinearMap)

omit [CompleteSpace H] in
private lemma diagonal_apply (A : H →L[ℂ] H) (x : K) (i : ι) :
    diagonal A x i = A (x i) := rfl

private lemma diagonal_inner [Fintype ι] (A : H →L[ℂ] H) (x y : K) :
    ⟪diagonal A x, y⟫ = ⟪x, diagonal (star A) y⟫ := by
  simp only [PiLp.inner_apply, diagonal_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

variable [Finite ι]

/-- Commutation on the finite Hilbert sum is determined by the operator entries. -/
private lemma diagonal_commutes (S : StarSubalgebra ℂ (H →L[ℂ] H)) {B : H →L[ℂ] H}
    (hB : B ∈ centralizer (centralizer (S : Set (H →L[ℂ] H)))) (P : K →L[ℂ] K)
    (hP : ∀ A ∈ S, ∀ y : K, P (diagonal A y) = diagonal A (P y)) (x : K) :
    P (diagonal B x) = diagonal B (P x) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  let row (i : ι) := (PiLp.proj 2 (fun _ : ι => H) i).comp (P.comp e.symm.toContinuousLinearMap)
  let entry (i j : ι) := (row i).comp (ContinuousLinearMap.single ℂ (fun _ : ι => H) j)
  have expand (y : K) (i : ι) : ∑ j, entry i j (y j) = P y i :=
    ContinuousLinearMap.sum_comp_single ℂ _ (row i) (e y)
  have entry_mem (i j : ι) : entry i j ∈ centralizer (S : Set (H →L[ℂ] H)) := by
    intro A hA
    ext v
    have hs : diagonal A (PiLp.single 2 j v : K) = PiLp.single 2 j (A v) := by
      ext k
      by_cases hk : k = j <;> simp [diagonal_apply, hk]
    have h := hP A hA (PiLp.single 2 j v)
    rw [hs] at h
    exact congrArg (fun y : K => y i) h.symm
  apply PiLp.ext
  intro i
  rw [diagonal_apply, ← expand (diagonal B x) i, ← expand x i, map_sum]
  exact Finset.sum_congr rfl fun j _ => DFunLike.congr_fun (hB _ (entry_mem i j)) (x j)

/-- The diagonal orbit of a tuple under the algebra is a linear subspace. -/
private noncomputable def orbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : K) :
    S →ₗ[ℂ] K where
  toFun A := diagonal (A : H →L[ℂ] H) x
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- The closed orbit contains the image of its generating tuple under the double commutant. -/
private lemma mem_closedOrbit (S : StarSubalgebra ℂ (H →L[ℂ] H)) {B : H →L[ℂ] H}
    (hB : B ∈ centralizer (centralizer (S : Set (H →L[ℂ] H)))) (x : K) :
    diagonal B x ∈ closure (Set.range (orbitMap S x)) := by
  let : Fintype ι := Fintype.ofFinite ι
  let V := (LinearMap.range (orbitMap S x)).topologicalClosure
  have invariant (A : H →L[ℂ] H) (hA : A ∈ S) : MapsTo (diagonal A) (V : Set K) V := by
    apply MapsTo.closure _ (diagonal A).continuous
    rintro _ ⟨C, rfl⟩
    exact ⟨⟨A * C, mul_mem hA C.property⟩, rfl⟩
  have projection_commutes (A : H →L[ℂ] H) (hA : A ∈ S) (y : K) :
      V.starProjection (diagonal A y) = diagonal A (V.starProjection y) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (invariant A hA (V.starProjection_apply_mem y))
    intro w hw
    rw [← map_sub, diagonal_inner]
    exact Submodule.starProjection_inner_eq_zero _ _ (invariant (star A) (star_mem hA) hw)
  have hx : x ∈ V := (LinearMap.range (orbitMap S x)).le_topologicalClosure
    ⟨1, by ext; rfl⟩
  have h := diagonal_commutes S hB V.starProjection projection_commutes x
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at h
  exact Submodule.starProjection_eq_self_iff.mp h

end Amplification

/-- A double-commutant element can be approximated on any finite set of vectors at once. -/
private lemma mem_strongClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) {B : H →L[ℂ] H}
    (hB : B ∈ centralizer (centralizer (S : Set (H →L[ℂ] H)))) :
    let toStrong := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
    toStrong B ∈ closure (toStrong '' (S : Set (H →L[ℂ] H))) := by
  classical
  intro toStrong
  have basis := (PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis
    (σ := RingHom.id ℂ) (E := H) (Metric.nhds_basis_ball (x := (0 : H)))).comap
      (fun C => C - toStrong B)
  rw [nhds_translation_sub] at basis
  apply (mem_closure_iff_nhds_basis basis).2
  rintro ⟨F, ε⟩ ⟨hF, hε⟩
  let : Fintype F := Fintype.ofFinite F
  let x : PiLp 2 (fun _ : F => H) := WithLp.toLp 2 (fun i : F => (i : H))
  obtain ⟨_, ⟨A, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp (mem_closedOrbit S hB x) ε hε
  refine ⟨toStrong A, ⟨A, A.property, rfl⟩, ?_⟩
  intro y hy
  have h := (PiLp.dist_apply_le (diagonal B x) (orbitMap S x A) ⟨y, hy⟩).trans_lt hdist
  change A.val y - B y ∈ Metric.ball 0 ε
  rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]
  exact h

omit [CompleteSpace H] in
private lemma weakImage_centralizer (s : Set (H →L[ℂ] H)) :
    ofCLM '' centralizer s = centralizer (ofCLM '' s) := by
  apply Set.ext
  rintro ⟨A⟩
  rw [ofCLM_injective.mem_set_image, mem_centralizer_iff, mem_centralizer_iff, forall_mem_image]
  simp only [← ofCLM_mul, ofCLM_injective.eq_iff]

end

set_option linter.dupNamespace false in
/-- **Von Neumann's double commutant theorem.** Let $H$ be a complex Hilbert space and let $S$ be
a unital $*$-subalgebra of the algebra of bounded linear operators on $H$. Write $S'$ for the
commutant of $S$, the set of bounded operators on $H$ that commute with every element of $S$.
The following are equivalent: $S$ equals its double commutant $S''$; $S$ is closed in the weak
operator topology; $S$ is closed in the strong operator topology, the topology of pointwise
convergence on $H$.

Source: J. von Neumann, *Zur Algebra der Funktionaloperationen und Theorie der normalen
Operatoren*, Math. Ann. 102 (1929) (double commutant theorem). Via leanprover/lean-eval@38361be,
problem `vonneumann_double_commutant`. -/
public theorem vonNeumann_doubleCommutant_tfae
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    List.TFAE
      [ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S
      , IsClosed
          (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H)))
      , IsClosed
          (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
            (S : Set (H →L[ℂ] H))) ] := by
  tfae_have 1 → 2 := by
    intro h
    rw [← h, weakImage_centralizer]
    exact Set.isClosed_centralizer _
  tfae_have 2 → 3 := by
    intro h
    have hc : Continuous (fun A : H →Lₚₜ[ℂ] H => ofCLM A) :=
      continuous_of_dual_apply_continuous fun x y => y.continuous.comp (continuous_eval_const x)
    convert h.preimage hc using 1
    ext A
    change A ∈ (fun T : H →L[ℂ] H => T) '' (S : Set _) ↔ ofCLM A ∈ ofCLM '' (S : Set _)
    exact Function.injective_id.mem_set_image.trans ofCLM_injective.mem_set_image.symm
  tfae_have 3 → 1 := by
    intro h
    apply Set.Subset.antisymm _ Set.subset_centralizer_centralizer
    intro B hB
    obtain ⟨A, hA, heq⟩ := h.closure_subset (mem_strongClosure S hB)
    exact (show A = B from heq) ▸ hA
  tfae_finish

end MathlibExt.Analysis.VonNeumannDoubleCommutantWanted.Analysis
