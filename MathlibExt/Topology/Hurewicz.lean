/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Topology/Hurewicz.lean` (leanprover/lean-eval), problem `hurewicz_h1_abelianization`,
at commit 38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/hurewicz_h1_abelianization.toml`, rev 1, submitter Kim Morrison, status
archived), for the definition `IntegralHomology` and the statement of
`hurewicz_h1_abelianization`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). The original evaluation problem was
converted to a Batteries wanted declaration in the `MathlibExt.Topology.HurewiczWanted`
namespace. This module moves the definition, the statement and their docstrings from
`WantedExt/Topology/HurewiczWanted.lean` and supplies a proof. Mathematical statements are
unchanged. Source: W. Hurewicz (1935); see Hatcher, *Algebraic Topology*, Theorem 2A.1. Knill,
*Some fundamental theorems in mathematics*, §153.
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Hurewicz theorem (degree 1): H₁ is the abelianization of π₁

For a path-connected space `X`, `hurewicz_h1_abelianization` identifies the abelianization of
the fundamental group with the first integral singular homology group `IntegralHomology 1 X`.
See §153 of the Knill survey.

## Proof

Write `C_n` for the integral singular `n`-chains of `X` and `B₁ ⊆ C₁` for the boundaries.
A path `γ` gives a singular `1`-simplex `⟨γ⟩` (precompose with `Δ¹ ≃ [0, 1]`). Explicit
singular `2`-simplices show that, modulo `B₁`, a constant path is `0`,
`⟨p · q⟩ = ⟨p⟩ + ⟨q⟩`, `⟨p⁻¹⟩ = -⟨p⟩`, and homotopic paths agree. So a loop at `x` defines a
class in `H₁`, and this gives a homomorphism from the abelianized fundamental group to `H₁`.

For the inverse, choose a path `c_y` from `x` to every point `y`. A singular `1`-simplex `σ`
from `a` to `b` is sent to the image in the abelianized fundamental group of the class of the
loop `c_a · σ · c_b⁻¹`. This vanishes on the boundary of every singular `2`-simplex because the
standard `2`-simplex is simply connected, so it induces a map from `H₁`. The two maps are mutually
inverse: on a cycle `z` the composite is `z - c(∂z) = z` modulo `B₁`, where `c` is the additive
map sending a point `y` to `⟨c_y⟩`.

`H₁` is computed as cycles modulo boundaries through `ShortComplex.abHomologyIso`.
-/

namespace MathlibExt.Topology.HurewiczWanted
namespace Topology.Hurewicz

open CategoryTheory AlgebraicTopology

set_option linter.dupNamespace false in
/-- **Integral singular homology.** For a natural number $n$ and a topological space $X$,
$H_n(X; \mathbb{Z})$ denotes the $n$-th singular homology group of $X$ with coefficients in
$\mathbb{Z}$, regarded as an abelian group. -/
public noncomputable abbrev IntegralHomology (n : ℕ) (X : Type) [TopologicalSpace X] :
    AddCommGrpCat :=
  ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)

open Limits Opposite Convexity
open scoped Simplicial

/-! ### Singular chains in low degrees -/

section Chains

variable (X : Type) [TopologicalSpace X]

/-- The singular simplicial set of `X`. -/
private noncomputable abbrev S : SSet := TopCat.toSSet.obj (TopCat.of X)

/-- The integral singular chain complex of `X`. -/
private noncomputable abbrev K : ChainComplex AddCommGrpCat ℕ :=
  (S X).chainComplex (AddCommGrpCat.of ℤ)

/-- The singular `1`-boundaries of `X`. -/
private noncomputable abbrev B : AddSubgroup ((K X).X 1) := ((K X).d 2 1).hom.range

variable {X}

/-- The chain given by a single singular simplex. -/
private noncomputable def gen {n : ℕ} (σ : (S X) _⦋n⦌) : (K X).X n :=
  ((S X).ιChainComplex (R := AddCommGrpCat.of ℤ) σ).hom (1 : ℤ)

private lemma d_gen_one (σ : (S X) _⦋1⦌) :
    ((K X).d 1 0).hom (gen σ) = gen ((S X).δ 0 σ) - gen ((S X).δ 1 σ) := by
  have h := congrArg (fun f ↦ f.hom (1 : ℤ))
    (SSet.ιChainComplex_d (X := S X) (R := AddCommGrpCat.of ℤ) (n := 0) σ)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  rw [gen, h]
  simp [Fin.sum_univ_two, gen, sub_eq_add_neg]

private lemma d_gen_two (τ : (S X) _⦋2⦌) :
    ((K X).d 2 1).hom (gen τ) =
      gen ((S X).δ 0 τ) - gen ((S X).δ 1 τ) + gen ((S X).δ 2 τ) := by
  have h := congrArg (fun f ↦ f.hom (1 : ℤ))
    (SSet.ιChainComplex_d (X := S X) (R := AddCommGrpCat.of ℤ) (n := 1) τ)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  rw [gen, h]
  simp [Fin.sum_univ_three, gen, sub_eq_add_neg]

/-- The additive map on singular chains with prescribed values on simplices. -/
private noncomputable def descGen {n : ℕ} {A : Type} [AddCommGroup A] (f : (S X) _⦋n⦌ → A) :
    (K X).X n →+ A :=
  (Sigma.desc (fun σ ↦ AddCommGrpCat.ofHom (zmultiplesHom A (f σ))) :
    (K X).X n ⟶ AddCommGrpCat.of A).hom

private lemma descGen_gen {n : ℕ} {A : Type} [AddCommGroup A] (f : (S X) _⦋n⦌ → A)
    (σ : (S X) _⦋n⦌) : descGen f (gen σ) = f σ := by
  simp only [descGen, gen, SSet.ιChainComplex]
  rw [← AddMonoidHom.comp_apply, ← AddCommGrpCat.hom_comp, Sigma.ι_comp_desc]
  simp

private lemma hom_ext_gen {n : ℕ} {A : Type} [AddCommGroup A] {φ ψ : (K X).X n →+ A}
    (h : ∀ σ : (S X) _⦋n⦌, φ (gen σ) = ψ (gen σ)) : φ = ψ := by
  have : AddCommGrpCat.ofHom φ = AddCommGrpCat.ofHom ψ := by
    refine SSet.chainComplex_hom_ext (fun σ ↦ ?_)
    ext1
    simpa [gen] using h σ
  simpa using congrArg AddCommGrpCat.Hom.hom this

private lemma boundary_mem (τ : (S X) _⦋2⦌) :
    gen ((S X).δ 0 τ) - gen ((S X).δ 1 τ) + gen ((S X).δ 2 τ) ∈ B X :=
  ⟨gen τ, d_gen_two τ⟩

end Chains

/-! ### Singular simplices as continuous maps -/

section Simplices

variable {X : Type} [TopologicalSpace X]

/-- The singular `1`-simplex given by a continuous map from the standard `1`-simplex. -/
private noncomputable def ofMap₁ (f : C(StdSimplex ℝ (Fin 2), X)) : (S X) _⦋1⦌ :=
  ((TopCat.of X).toSSetObjEquiv (op ⦋1⦌)).symm f

/-- The singular `2`-simplex given by a continuous map from the standard `2`-simplex. -/
private noncomputable def ofMap₂ (f : C(StdSimplex ℝ (Fin 3), X)) : (S X) _⦋2⦌ :=
  ((TopCat.of X).toSSetObjEquiv (op ⦋2⦌)).symm f

/-- The continuous map underlying a singular `1`-simplex. -/
private noncomputable def toMap₁ (σ : (S X) _⦋1⦌) : C(StdSimplex ℝ (Fin 2), X) :=
  (TopCat.of X).toSSetObjEquiv (op ⦋1⦌) σ

/-- The continuous map underlying a singular `2`-simplex. -/
private noncomputable def toMap₂ (τ : (S X) _⦋2⦌) : C(StdSimplex ℝ (Fin 3), X) :=
  (TopCat.of X).toSSetObjEquiv (op ⦋2⦌) τ

private lemma ofMap₁_toMap₁ (σ : (S X) _⦋1⦌) : ofMap₁ (toMap₁ σ) = σ :=
  Equiv.symm_apply_apply _ _

private lemma toMap₁_ofMap₁ (f : C(StdSimplex ℝ (Fin 2), X)) : toMap₁ (ofMap₁ f) = f :=
  Equiv.apply_symm_apply _ _

/-- The `i`-th face inclusion of the standard `1`-simplex into the standard `2`-simplex. -/
private noncomputable def face (i : Fin 3) : C(StdSimplex ℝ (Fin 2), StdSimplex ℝ (Fin 3)) :=
  ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩

private lemma δ_ofMap₂ (f : C(StdSimplex ℝ (Fin 3), X)) (i : Fin 3) :
    (S X).δ i (ofMap₂ f) = ofMap₁ (f.comp (face i)) := rfl

/-- Vertices of the singular simplicial set are points of `X`. -/
private noncomputable abbrev vtx : (S X) _⦋0⦌ ≃ X := TopCat.toSSetObj₀Equiv

private lemma vtx_δ_zero (σ : (S X) _⦋1⦌) :
    vtx ((S X).δ 0 σ) = toMap₁ σ (StdSimplex.single 1) := by
  rw [vtx, TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply]
  simp [toMap₁, Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (.single 0),
    StdSimplex.map_single]

private lemma vtx_δ_one (σ : (S X) _⦋1⦌) :
    vtx ((S X).δ 1 σ) = toMap₁ σ (StdSimplex.single 0) := by
  rw [vtx, TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply]
  simp [toMap₁, Subsingleton.elim (default : StdSimplex ℝ (Fin 1)) (.single 0),
    StdSimplex.map_single]

private lemma δ_zero_ofMap₁ (f : C(StdSimplex ℝ (Fin 2), X)) :
    (S X).δ 0 (ofMap₁ f) = vtx.symm (f (StdSimplex.single 1)) := by
  rw [Equiv.eq_symm_apply, vtx_δ_zero, toMap₁_ofMap₁]

private lemma δ_one_ofMap₁ (f : C(StdSimplex ℝ (Fin 2), X)) :
    (S X).δ 1 (ofMap₁ f) = vtx.symm (f (StdSimplex.single 0)) := by
  rw [Equiv.eq_symm_apply, vtx_δ_one, toMap₁_ofMap₁]

private lemma weights_face_succAbove (i : Fin 3) (w : StdSimplex ℝ (Fin 2)) (j : Fin 2) :
    (face i w).weights (i.succAbove j) = w.weights j := by
  simp [face, StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]

private lemma weights_face_self (i : Fin 3) (w : StdSimplex ℝ (Fin 2)) :
    (face i w).weights i = 0 := by
  simp only [face, ContinuousMap.coe_mk, StdSimplex.weights_map]
  apply Finsupp.mapDomain_of_notMem_range
  simp

private lemma face0 (w : StdSimplex ℝ (Fin 2)) :
    (face 0 w).weights 0 = 0 ∧ (face 0 w).weights 1 = w.weights 0 ∧
      (face 0 w).weights 2 = w.weights 1 :=
  ⟨weights_face_self _ _, weights_face_succAbove (0 : Fin 3) w 0,
    weights_face_succAbove (0 : Fin 3) w 1⟩

private lemma face1 (w : StdSimplex ℝ (Fin 2)) :
    (face 1 w).weights 0 = w.weights 0 ∧ (face 1 w).weights 1 = 0 ∧
      (face 1 w).weights 2 = w.weights 1 :=
  ⟨weights_face_succAbove (1 : Fin 3) w 0, weights_face_self _ _,
    weights_face_succAbove (1 : Fin 3) w 1⟩

private lemma face2 (w : StdSimplex ℝ (Fin 2)) :
    (face 2 w).weights 0 = w.weights 0 ∧ (face 2 w).weights 1 = w.weights 1 ∧
      (face 2 w).weights 2 = 0 :=
  ⟨weights_face_succAbove (2 : Fin 3) w 0, weights_face_succAbove (2 : Fin 3) w 1,
    weights_face_self _ _⟩

private lemma face_single (i : Fin 3) (j : Fin 2) :
    face i (StdSimplex.single j) = StdSimplex.single (i.succAbove j) := by
  simp [face, StdSimplex.map_single]

private lemma total_fin_three (w : StdSimplex ℝ (Fin 3)) :
    w.weights 0 + w.weights 1 + w.weights 2 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_three]

private lemma homeomorphI_coe (w : StdSimplex ℝ (Fin 2)) :
    (StdSimplex.homeomorphI w : ℝ) = w.weights 1 :=
  StdSimplex.homeomorphI_apply_coe w

/-- The singular `1`-simplex traced by a path. -/
private noncomputable def pathSimplex {a b : X} (γ : Path a b) : (S X) _⦋1⦌ :=
  ofMap₁ (γ.toContinuousMap.comp ⟨StdSimplex.homeomorphI, StdSimplex.homeomorphI.continuous⟩)

private lemma δ_zero_pathSimplex {a b : X} (γ : Path a b) :
    (S X).δ 0 (pathSimplex γ) = vtx.symm b := by
  rw [pathSimplex, δ_zero_ofMap₁]
  simp

private lemma δ_one_pathSimplex {a b : X} (γ : Path a b) :
    (S X).δ 1 (pathSimplex γ) = vtx.symm a := by
  rw [pathSimplex, δ_one_ofMap₁]
  simp

private lemma path_congr {a b : X} (γ : Path a b) {s t : unitInterval} (h : (s : ℝ) = t) :
    γ s = γ t :=
  congrArg γ (Subtype.ext h)

end Simplices

/-! ### Paths modulo boundaries -/

section PathRelations

variable {X : Type} [TopologicalSpace X]

private lemma refl_mem (a : X) : gen (pathSimplex (Path.refl a)) ∈ B X := by
  have h := boundary_mem (ofMap₂ (ContinuousMap.const (StdSimplex ℝ (Fin 3)) a))
  simp only [δ_ofMap₂, ContinuousMap.const_comp] at h
  have e : pathSimplex (Path.refl a) = ofMap₁ (ContinuousMap.const _ a) := rfl
  rw [e]
  simpa using h

private lemma rT_mem (w : StdSimplex ℝ (Fin 3)) :
    w.weights 1 / 2 + w.weights 2 ∈ unitInterval := by
  have := total_fin_three w
  have := w.weights_nonneg 0
  have := w.weights_nonneg 1
  have := w.weights_nonneg 2
  constructor <;> linarith

/-- The map `Δ² → [0, 1]` whose composite with `p · q` has faces `q`, `p · q` and `p`. -/
private noncomputable def rT : C(StdSimplex ℝ (Fin 3), unitInterval) :=
  ⟨fun w ↦ ⟨_, rT_mem w⟩, Continuous.subtype_mk (by fun_prop) rT_mem⟩

private lemma rT_coe (w : StdSimplex ℝ (Fin 3)) :
    (rT w : ℝ) = w.weights 1 / 2 + w.weights 2 := rfl

private lemma trans_mem {a b c : X} (p : Path a b) (q : Path b c) :
    gen (pathSimplex p) + gen (pathSimplex q) - gen (pathSimplex (p.trans q)) ∈ B X := by
  have h := boundary_mem (ofMap₂ ((p.trans q).toContinuousMap.comp rT))
  have e0 : (S X).δ 0 (ofMap₂ ((p.trans q).toContinuousMap.comp rT)) = pathSimplex q := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face0 w
    have ht := w.total_fin_two
    have hn0 := w.weights_nonneg 0
    have hn1 := w.weights_nonneg 1
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap]
    rw [Path.trans_apply]
    split_ifs with hle
    · have hw : w.weights 1 = 0 := by
        simp only [rT_coe, h1, h2] at hle; linarith
      rw [path_congr p (t := 1) (by simp only [rT_coe, h1, h2]; push_cast; linarith),
        path_congr q (t := 0) (by simp [homeomorphI_coe, hw]), p.target, q.source]
    · apply path_congr
      simp only [rT_coe, h1, h2, homeomorphI_coe]
      linarith
  have e1 : (S X).δ 1 (ofMap₂ ((p.trans q).toContinuousMap.comp rT)) =
      pathSimplex (p.trans q) := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face1 w
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap]
    apply path_congr
    simp [rT_coe, h1, h2, homeomorphI_coe]
  have e2 : (S X).δ 2 (ofMap₂ ((p.trans q).toContinuousMap.comp rT)) = pathSimplex p := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face2 w
    have hl := w.weights_apply_le_one 1
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap]
    rw [Path.trans_apply]
    split_ifs with hle
    · apply path_congr
      simp only [rT_coe, h1, h2, homeomorphI_coe]
      ring
    · exfalso
      simp only [rT_coe, h1, h2] at hle
      linarith
  rw [e0, e1, e2] at h
  convert h using 1
  abel

private lemma rS_mem (w : StdSimplex ℝ (Fin 3)) : w.weights 1 ∈ unitInterval :=
  ⟨w.weights_nonneg 1, w.weights_apply_le_one 1⟩

/-- The map `Δ² → [0, 1]` whose composite with `p` has faces `p⁻¹`, a constant path and `p`. -/
private noncomputable def rS : C(StdSimplex ℝ (Fin 3), unitInterval) :=
  ⟨fun w ↦ ⟨_, rS_mem w⟩, Continuous.subtype_mk (by fun_prop) rS_mem⟩

private lemma rS_coe (w : StdSimplex ℝ (Fin 3)) : (rS w : ℝ) = w.weights 1 := rfl

private lemma symm_mem {a b : X} (p : Path a b) :
    gen (pathSimplex p) + gen (pathSimplex p.symm) ∈ B X := by
  have h := boundary_mem (ofMap₂ (p.toContinuousMap.comp rS))
  have e0 : (S X).δ 0 (ofMap₂ (p.toContinuousMap.comp rS)) = pathSimplex p.symm := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face0 w
    have ht := w.total_fin_two
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap,
      Path.symm_apply]
    apply path_congr
    simp only [rS_coe, h1, unitInterval.coe_symm_eq, homeomorphI_coe]
    linarith
  have e1 : (S X).δ 1 (ofMap₂ (p.toContinuousMap.comp rS)) = pathSimplex (Path.refl a) := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face1 w
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap,
      Path.refl_apply]
    rw [path_congr p (t := 0) (by simp [rS_coe, h1]), p.source]
  have e2 : (S X).δ 2 (ofMap₂ (p.toContinuousMap.comp rS)) = pathSimplex p := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face2 w
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap]
    apply path_congr
    simp [rS_coe, h1, homeomorphI_coe]
  rw [e0, e1, e2] at h
  have h' := add_mem h (refl_mem (X := X) a)
  convert h' using 1
  abel

private lemma diag_mem₁ (w : StdSimplex ℝ (Fin 3)) : w.weights 2 ∈ unitInterval :=
  ⟨w.weights_nonneg 2, w.weights_apply_le_one 2⟩

private lemma diag_mem₂ (w : StdSimplex ℝ (Fin 3)) :
    w.weights 1 + w.weights 2 ∈ unitInterval := by
  have := total_fin_three w
  have := w.weights_nonneg 0
  have := w.weights_nonneg 1
  have := w.weights_nonneg 2
  constructor <;> linarith

/-- The affine map from `Δ²` onto the triangle of `[0, 1]²` above the diagonal. -/
private noncomputable def g₁ : C(StdSimplex ℝ (Fin 3), unitInterval × unitInterval) :=
  ⟨fun w ↦ (⟨_, diag_mem₁ w⟩, ⟨_, diag_mem₂ w⟩),
    Continuous.prodMk (Continuous.subtype_mk (by fun_prop) diag_mem₁)
      (Continuous.subtype_mk (by fun_prop) diag_mem₂)⟩

/-- The affine map from `Δ²` onto the triangle of `[0, 1]²` below the diagonal. -/
private noncomputable def g₂ : C(StdSimplex ℝ (Fin 3), unitInterval × unitInterval) :=
  ⟨fun w ↦ (⟨_, diag_mem₂ w⟩, ⟨_, diag_mem₁ w⟩),
    Continuous.prodMk (Continuous.subtype_mk (by fun_prop) diag_mem₂)
      (Continuous.subtype_mk (by fun_prop) diag_mem₁)⟩

private lemma g₁_fst (w : StdSimplex ℝ (Fin 3)) : ((g₁ w).1 : ℝ) = w.weights 2 := rfl

private lemma g₁_snd (w : StdSimplex ℝ (Fin 3)) :
    ((g₁ w).2 : ℝ) = w.weights 1 + w.weights 2 := rfl

private lemma g₂_fst (w : StdSimplex ℝ (Fin 3)) :
    ((g₂ w).1 : ℝ) = w.weights 1 + w.weights 2 := rfl

private lemma g₂_snd (w : StdSimplex ℝ (Fin 3)) : ((g₂ w).2 : ℝ) = w.weights 2 := rfl

private lemma homotopic_mem {a b : X} {p q : Path a b} (hpq : p.Homotopic q) :
    gen (pathSimplex p) - gen (pathSimplex q) ∈ B X := by
  obtain ⟨F⟩ := hpq
  let f : C(unitInterval × unitInterval, X) := ⟨fun st ↦ F st, map_continuous F⟩
  have h₁ := boundary_mem (ofMap₂ (f.comp g₁))
  have h₂ := boundary_mem (ofMap₂ (f.comp g₂))
  have e10 : (S X).δ 0 (ofMap₂ (f.comp g₁)) = pathSimplex (Path.refl b) := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face0 w
    have ht := w.total_fin_two
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap,
      Path.refl_apply, f]
    rw [show g₁ (face 0 w) = ((g₁ (face 0 w)).1, 1) from
      Prod.ext rfl (Subtype.ext (by simp [g₁_snd, h1, h2, ht])), F.target]
  have e12 : (S X).δ 2 (ofMap₂ (f.comp g₁)) = pathSimplex p := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face2 w
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap, f]
    rw [show g₁ (face 2 w) = (0, StdSimplex.homeomorphI w) from
      Prod.ext (Subtype.ext (by simp [g₁_fst, h2]))
        (Subtype.ext (by simp [g₁_snd, h1, h2, homeomorphI_coe]))]
    exact F.apply_zero _
  have e20 : (S X).δ 0 (ofMap₂ (f.comp g₂)) = pathSimplex q := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face0 w
    have ht := w.total_fin_two
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap, f]
    rw [show g₂ (face 0 w) = (1, StdSimplex.homeomorphI w) from
      Prod.ext (Subtype.ext (by simp [g₂_fst, h1, h2, ht]))
        (Subtype.ext (by simp [g₂_snd, h2, homeomorphI_coe]))]
    exact F.apply_one _
  have e22 : (S X).δ 2 (ofMap₂ (f.comp g₂)) = pathSimplex (Path.refl a) := by
    rw [δ_ofMap₂, pathSimplex]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face2 w
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Path.coe_toContinuousMap,
      Path.refl_apply, f]
    rw [show g₂ (face 2 w) = ((g₂ (face 2 w)).1, 0) from
      Prod.ext rfl (Subtype.ext (by simp [g₂_snd, h2])), F.source]
  have e11 : (S X).δ 1 (ofMap₂ (f.comp g₁)) = (S X).δ 1 (ofMap₂ (f.comp g₂)) := by
    rw [δ_ofMap₂, δ_ofMap₂]
    congr 1
    ext w
    obtain ⟨h0, h1, h2⟩ := face1 w
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, f]
    congr 1
    exact Prod.ext (Subtype.ext (by simp [g₁_fst, g₂_fst, h1, h2]))
      (Subtype.ext (by simp [g₁_snd, g₂_snd, h1, h2]))
  rw [e10, e12, e11] at h₁
  rw [e20, e22] at h₂
  have h := add_mem (sub_mem h₁ h₂) (sub_mem (refl_mem (X := X) a) (refl_mem (X := X) b))
  convert h using 1
  abel

end PathRelations

/-! ### The Hurewicz map -/

section HurewiczMap

variable {X : Type} [TopologicalSpace X] (x : X)

variable (X) in
/-- The short complex `C₂ ⟶ C₁ ⟶ C₀` of singular chains of `X`. -/
private noncomputable abbrev SC := (K X).sc' 2 1 0

variable (X) in
/-- First singular homology computed as cycles modulo boundaries. -/
private abbrev Q := ↥(SC X).g.hom.ker ⧸ (SC X).abToCycles.range

/-- The abelianized fundamental group, written additively. -/
private abbrev Ab := Additive (Group.Abelianization (FundamentalGroup X x))

private lemma cycle_loop (γ : Path x x) : gen (pathSimplex γ) ∈ (SC X).g.hom.ker := by
  rw [AddMonoidHom.mem_ker]
  change ((K X).d 1 0).hom (gen (pathSimplex γ)) = 0
  rw [d_gen_one, δ_zero_pathSimplex, δ_one_pathSimplex, sub_self]

/-- The homology class of the `1`-cycle traced by a loop. -/
private noncomputable def h₀ (γ : Path x x) : Q X :=
  QuotientAddGroup.mk ⟨gen (pathSimplex γ), cycle_loop x γ⟩

omit x in
private lemma mk_eq_mk {z z' : (SC X).g.hom.ker} (h : (z.1 - z'.1 : (K X).X 1) ∈ B X) :
    (QuotientAddGroup.mk z : Q X) = QuotientAddGroup.mk z' := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, hw⟩ := h
  refine ⟨-w, Subtype.ext ?_⟩
  simp only [ShortComplex.abToCycles_apply_coe, map_neg, AddSubgroup.coe_add,
    AddSubgroup.coe_neg]
  change -((K X).d 2 1).hom w = _
  rw [hw]
  abel

/-- The homology class of a loop class. -/
private noncomputable def h₁ (g : FundamentalGroup X x) : Q X :=
  Quotient.lift (s := Path.Homotopic.setoid x x) (h₀ x)
    (fun _ _ hγ ↦ mk_eq_mk (homotopic_mem hγ)) (FundamentalGroup.toPath g)

private lemma h₁_fromPath (γ : Path x x) :
    h₁ x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = h₀ x γ := rfl

private lemma h₁_mul (g g' : FundamentalGroup X x) : h₁ x (g * g') = h₁ x g + h₁ x g' := by
  obtain ⟨q⟩ := g
  obtain ⟨q'⟩ := g'
  induction q using Path.Homotopic.Quotient.ind with | mk γ =>
  induction q' using Path.Homotopic.Quotient.ind with | mk γ' =>
  change h₁ x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ'.trans γ))) = _
  rw [h₁_fromPath, h₁_fromPath, h₁_fromPath, h₀, h₀, h₀, ← QuotientAddGroup.mk_add]
  apply mk_eq_mk
  change gen (pathSimplex (γ'.trans γ)) - (gen (pathSimplex γ) + gen (pathSimplex γ')) ∈ B X
  convert neg_mem (trans_mem γ' γ) using 1
  abel

/-- The Hurewicz map from the abelianized fundamental group to first homology. -/
private noncomputable def χ : Ab x →+ Q X :=
  MonoidHom.toAdditiveLeft (Group.Abelianization.lift
    (MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd (h₁ x g)) (fun g g' ↦ by
      rw [h₁_mul, ofAdd_add])))

private lemma χ_of (g : FundamentalGroup X x) :
    χ x (Additive.ofMul (Group.Abelianization.of g)) = h₁ x g := rfl

end HurewiczMap

/-! ### The inverse map -/

section Inverse

/-- The standard `2`-simplex is simply connected. -/
private lemma simplyConnected_stdSimplex : SimplyConnectedSpace (StdSimplex ℝ (Fin 3)) := by
  have he := StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)
  have hc : ContractibleSpace (Set.range fun t : StdSimplex ℝ (Fin 3) ↦ ⇑t.weights) := by
    apply Convex.contractibleSpace
    · rw [StdSimplex.range_toFun_comp_weights]
      intro s hs t ht a b ha hb hab
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hs ht ⊢
      refine ⟨fun i ↦ ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hs.1 i
        have := ht.1 i
        positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hs.2, ht.2]
        linarith
    · exact Set.range_nonempty _
  have := he.toHomeomorph.contractibleSpace
  infer_instance

/-- The standard path from the first to the second vertex of the standard `1`-simplex. -/
private noncomputable def stdPath :
    Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 2)) (StdSimplex.single 1) where
  toFun t := StdSimplex.homeomorphI.symm t
  continuous_toFun := StdSimplex.homeomorphI.symm.continuous
  source' := StdSimplex.homeomorphI_symm_zero
  target' := StdSimplex.homeomorphI_symm_one

variable {X : Type} [TopologicalSpace X]

/-- The path traced by a singular `1`-simplex. -/
private noncomputable def edge (σ : (S X) _⦋1⦌) :
    Path (toMap₁ σ (StdSimplex.single 0)) (toMap₁ σ (StdSimplex.single 1)) :=
  stdPath.map (toMap₁ σ).continuous

private lemma pathSimplex_edge (σ : (S X) _⦋1⦌) : pathSimplex (edge σ) = σ := by
  conv_rhs => rw [← ofMap₁_toMap₁ σ]
  rw [pathSimplex]
  congr 1
  ext w
  simp [edge, stdPath]

private lemma symm_trans_cancel {a b c : X} (γ : Path.Homotopic.Quotient a b)
    (δ : Path.Homotopic.Quotient b c) : γ.symm.trans (γ.trans δ) = δ := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

variable [PathConnectedSpace X] (x : X)

/-- A chosen path from the base point to `y`. -/
private noncomputable def basePath (y : X) : Path x y := PathConnectedSpace.somePath x y

/-- The loop at the base point that runs along a path, using the chosen paths to its ends. -/
private noncomputable def loop {a b : X} (γ : Path a b) : Path x x :=
  ((basePath x a).trans γ).trans (basePath x b).symm

/-- The loop class attached to a singular `1`-simplex. -/
private noncomputable def Φ (σ : (S X) _⦋1⦌) : FundamentalGroup X x :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loop x (edge σ)))

private lemma mk_loop {a b : X} (γ : Path a b) :
    Path.Homotopic.Quotient.mk (loop x γ) =
      ((Path.Homotopic.Quotient.mk (basePath x a)).trans (Path.Homotopic.Quotient.mk γ)).trans
        (Path.Homotopic.Quotient.mk (basePath x b)).symm := rfl

private lemma loop_congr {a b a' b' : X} (γ : Path a b) (γ' : Path a' b')
    (h : ∀ t, γ t = γ' t) :
    Path.Homotopic.Quotient.mk (loop x γ) = Path.Homotopic.Quotient.mk (loop x γ') := by
  have ha : a = a' := by rw [← γ.source, ← γ'.source, h]
  have hb : b = b' := by rw [← γ.target, ← γ'.target, h]
  subst ha hb
  obtain rfl : γ = γ' := Path.ext (funext h)
  rfl

private lemma Φ_pathSimplex {a b : X} (γ : Path a b) :
    Φ x (pathSimplex γ) = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loop x γ)) := by
  rw [Φ]
  congr 1
  apply loop_congr
  intro t
  change toMap₁ (pathSimplex γ) (stdPath t) = γ t
  rw [pathSimplex, toMap₁_ofMap₁]
  simp [stdPath]

private lemma key_rel {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (g : C(Y, X))
    {a b b' c a' c' : Y} (hb : b = b') (ha : a = a') (hc : c = c') (m : Path a b)
    (m' : Path b' c) (m'' : Path a' c') :
    (Path.Homotopic.Quotient.mk (loop x (m.map g.continuous))).trans
        (Path.Homotopic.Quotient.mk (loop x (m'.map g.continuous))) =
      Path.Homotopic.Quotient.mk (loop x (m''.map g.continuous)) := by
  subst hb ha hc
  have key : (Path.Homotopic.Quotient.mk (m.map g.continuous)).trans
      (Path.Homotopic.Quotient.mk (m'.map g.continuous)) =
        Path.Homotopic.Quotient.mk (m''.map g.continuous) := by
    rw [← Path.Homotopic.Quotient.mk_trans, ← Path.map_trans, Path.Homotopic.Quotient.eq]
    exact (SimplyConnectedSpace.paths_homotopic _ _).map g
  simp only [mk_loop, Path.Homotopic.Quotient.trans_assoc, symm_trans_cancel]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (m.map g.continuous)),
    key]

private lemma Φ_rel (τ : (S X) _⦋2⦌) :
    Φ x ((S X).δ 0 τ) * Φ x ((S X).δ 2 τ) = Φ x ((S X).δ 1 τ) := by
  have := simplyConnected_stdSimplex
  rw [FundamentalGroup.mul_def]
  exact congrArg FundamentalGroup.fromPath (key_rel x (toMap₂ τ)
    (by simp [face_single]; rfl) (by simp [face_single]) (by simp [face_single])
    (stdPath.map (face 2).continuous) (stdPath.map (face 0).continuous)
    (stdPath.map (face 1).continuous))

private lemma Φ_ab_rel (τ : (S X) _⦋2⦌) :
    Additive.ofMul (Group.Abelianization.of (Φ x ((S X).δ 0 τ))) -
      Additive.ofMul (Group.Abelianization.of (Φ x ((S X).δ 1 τ))) +
        Additive.ofMul (Group.Abelianization.of (Φ x ((S X).δ 2 τ))) = 0 := by
  rw [← Φ_rel x τ, map_mul, ofMul_mul]
  abel

/-- The inverse of the Hurewicz map on `1`-chains. -/
private noncomputable def φ₁ : (K X).X 1 →+ Ab x :=
  descGen (fun σ ↦ Additive.ofMul (Group.Abelianization.of (Φ x σ)))

private lemma φ₁_gen (σ : (S X) _⦋1⦌) :
    φ₁ x (gen σ) = Additive.ofMul (Group.Abelianization.of (Φ x σ)) :=
  descGen_gen _ _

private lemma φ₁_d (w : (K X).X 2) : φ₁ x (((K X).d 2 1).hom w) = 0 := by
  have : (φ₁ x).comp ((K X).d 2 1).hom = 0 := hom_ext_gen (fun τ ↦ by
    simp only [AddMonoidHom.comp_apply, d_gen_two, map_add, map_sub, φ₁_gen,
      AddMonoidHom.zero_apply]
    exact Φ_ab_rel x τ)
  exact DFunLike.congr_fun this w

/-- The inverse of the Hurewicz map. -/
private noncomputable def ψ : Q X →+ Ab x :=
  QuotientAddGroup.lift _ ((φ₁ x).comp (SC X).g.hom.ker.subtype) (by
    rintro _ ⟨w, rfl⟩
    exact (AddMonoidHom.mem_ker).mpr (φ₁_d x w))

private lemma ψ_mk (z : (SC X).g.hom.ker) : ψ x (QuotientAddGroup.mk z) = φ₁ x z.1 := rfl

/-- The `1`-chains given by the chosen paths from the base point to each vertex. -/
private noncomputable def Γ : (K X).X 0 →+ (K X).X 1 :=
  descGen (fun v ↦ gen (pathSimplex (basePath x (vtx v))))

/-- The map `c ↦ c - Γ (∂ c)`, which takes values in the cycles and fixes them. -/
private noncomputable def E : (K X).X 1 →+ (K X).X 1 :=
  AddMonoidHom.id _ - (Γ x).comp ((K X).d 1 0).hom

private lemma E_cycle (c : (K X).X 1) : E x c ∈ (SC X).g.hom.ker := by
  have : ((K X).d 1 0).hom.comp (E x) = 0 := hom_ext_gen (fun σ ↦ by
    simp only [E, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      map_sub, d_gen_one, Γ, descGen_gen, δ_zero_pathSimplex, δ_one_pathSimplex,
      Equiv.symm_apply_apply, AddMonoidHom.zero_apply]
    abel)
  exact (AddMonoidHom.mem_ker).mpr (DFunLike.congr_fun this c)

private lemma χ_φ₁ (c : (K X).X 1) :
    χ x (φ₁ x c) = QuotientAddGroup.mk ⟨E x c, E_cycle x c⟩ := by
  have : (χ x).comp (φ₁ x) =
      (QuotientAddGroup.mk' _).comp ((E x).codRestrict _ (E_cycle x)) := by
    refine hom_ext_gen (fun σ ↦ ?_)
    rw [AddMonoidHom.comp_apply, φ₁_gen, χ_of, Φ, h₁_fromPath, h₀, AddMonoidHom.comp_apply,
      QuotientAddGroup.mk'_apply]
    apply mk_eq_mk
    change gen (pathSimplex (loop x (edge σ))) - E x (gen σ) ∈ B X
    have h1 := trans_mem ((basePath x _).trans (edge σ)) (basePath x _).symm
    have h2 := trans_mem (basePath x _) (edge σ)
    have h3 := symm_mem (basePath x (toMap₁ σ (StdSimplex.single 1)))
    rw [pathSimplex_edge] at h2
    have h := add_mem (neg_mem (add_mem h1 h2)) h3
    convert h using 1
    simp only [E, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, AddMonoidHom.comp_apply,
      d_gen_one, map_sub, Γ, descGen_gen]
    rw [vtx_δ_zero, vtx_δ_one, loop]
    abel
  exact DFunLike.congr_fun this c

private lemma ψ_χ (a : Ab x) : ψ x (χ x a) = a := by
  obtain ⟨g, hg⟩ := Group.Abelianization.surjective_of (G := FundamentalGroup X x)
    (Additive.toMul a)
  have ha : a = Additive.ofMul (Group.Abelianization.of g) := by rw [hg, ofMul_toMul]
  subst ha
  obtain ⟨q⟩ := g
  induction q using Path.Homotopic.Quotient.ind with | mk γ =>
  change ψ x (h₁ x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) = _
  rw [h₁_fromPath, h₀, ψ_mk, φ₁_gen, Φ_pathSimplex]
  congr 1
  let c : FundamentalGroup X x :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basePath x x))
  have hc : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loop x γ)) =
      c⁻¹ * (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) * c) := rfl
  rw [hc, map_mul, map_mul, map_inv, mul_comm (Group.Abelianization.of _)
    (Group.Abelianization.of c), inv_mul_cancel_left]

private lemma χ_ψ (q : Q X) : χ x (ψ x q) = q := by
  induction q using QuotientAddGroup.induction_on with | H z =>
  rw [ψ_mk, χ_φ₁]
  congr 1
  apply Subtype.ext
  have hz : ((K X).d 1 0).hom z.1 = 0 := z.2
  change E x z.1 = z.1
  simp [E, hz]

/-- The Hurewicz isomorphism onto first homology computed as cycles modulo boundaries. -/
private noncomputable def hurewiczEquiv : Ab x ≃+ Q X where
  toFun := χ x
  invFun := ψ x
  left_inv := ψ_χ x
  right_inv := χ_ψ x
  map_add' := (χ x).map_add

end Inverse

/-- First integral singular homology agrees with cycles modulo boundaries. -/
private noncomputable def homologyIso (X : Type) [TopologicalSpace X] :
    IntegralHomology 1 X ≅ AddCommGrpCat.of (Q X) :=
  ShortComplex.homologyMapIso ((K X).isoSc' 2 1 0 (by simp) (by simp)) ≪≫ (SC X).abHomologyIso

set_option linter.dupNamespace false in
/- **Hurewicz (n = 1).** For a path-connected space `X`, `H₁(X;ℤ)` is the
abelianization of `π₁(X, x)`. -/
/-- **First homology is the abelianized fundamental group.** Let $X$ be a path-connected
topological space and let $x \in X$. Then the abelianization of the fundamental group
$\pi_1(X, x)$ is isomorphic, as a group, to the first integral singular homology group
$H_1(X; \mathbb{Z})$ of $X$.

Source: W. Hurewicz (1935); see Hatcher, *Algebraic Topology*, Theorem 2A.1. Knill, *Some
fundamental theorems in mathematics*, §153. Via leanprover/lean-eval@38361be, problem
`hurewicz_h1_abelianization`. -/
public theorem hurewicz_h1_abelianization
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Nonempty (Additive (Group.Abelianization (FundamentalGroup X x)) ≃+
      (IntegralHomology 1 X : Type)) :=
  ⟨(hurewiczEquiv x).trans (homologyIso X).addCommGroupIsoToAddEquiv.symm⟩

end Topology.Hurewicz

end MathlibExt.Topology.HurewiczWanted
