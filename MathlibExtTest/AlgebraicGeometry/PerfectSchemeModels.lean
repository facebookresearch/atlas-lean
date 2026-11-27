/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PerfectSchemeModels
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Lean.Elab.Tactic.Omega

/-! The ordinary affine F_2-line is not perfect: its coordinate X has
no square root. The contract therefore excludes confusing an ordinary
deperfection with the actual perfect geometric output.
-/

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PerfectSchemeModels

noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private lemma coordinate_not_square :
    ¬ Function.Surjective (fun f : Polynomial (ZMod 2) ↦ f ^ 2) := by
  intro h
  obtain ⟨f, hf⟩ := h Polynomial.X
  have hd := congrArg Polynomial.natDegree hf
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X] at hd
  omega

example : ¬ IsPerfect 2 (Over.mk
    (Spec.algebraMap (ZMod 2) (Polynomial (ZMod 2)))) := by
  intro h
  change ∀ U : (Spec (.of (Polynomial (ZMod 2)))).Opens, IsAffineOpen U →
    Function.Bijective (fun x : Γ(Spec (.of (Polynomial (ZMod 2))), U) ↦ x ^ 2) at h
  let e := Scheme.ΓSpecIso (.of (Polynomial (ZMod 2)))
  have hs := (h ⊤ (isAffineOpen_top (Spec (.of (Polynomial (ZMod 2)))))).2
  apply coordinate_not_square
  intro a
  obtain ⟨b, hb⟩ := hs (e.inv a)
  refine ⟨e.hom b, ?_⟩
  have hh := congrArg e.hom hb
  simpa only [map_pow, Iso.inv_hom_id_apply] using hh
