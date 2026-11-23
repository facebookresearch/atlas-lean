/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NormalBasisMapRotationIffConj
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Tests for rotation orbits of normal basis coordinates and conjugate elements -/

open MetaMathlibExt

-- Rotating the coordinates one step does not change the minimal polynomial over `F`. No `Fintype`
-- instance on `K` is needed: the theorem only assumes that `F` is finite.
example (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K] (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ))))
    (a : Fin n → F) :
    minpoly F (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) =
      minpoly F (∑ i, (a ∘ ⇑(finRotate n)) i • β ^ (Fintype.card F ^ (i : ℕ))) :=
  (normalBasisMap_rotation_iff_conj F K n hn β hβ a (a ∘ ⇑(finRotate n))).mp
    (comp_finRotate_mem_tupleRotationOrbit a)

-- If an automorphism of `K` over `F` sends `Φ a` to `Φ b`, then `b` is a rotation of `a`.
example (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K] (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ))))
    (a b : Fin n → F) (σ : K ≃ₐ[F] K)
    (h : σ (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) =
      ∑ i, b i • β ^ (Fintype.card F ^ (i : ℕ))) :
    b ∈ tupleRotationOrbit a :=
  (normalBasisMap_rotation_iff_conj F K n hn β hβ a b).mpr (by rw [← h, minpoly.algEquiv_eq])

-- The hypotheses can be met: for `K = F = ZMod 3` (so `n = 1`) take `β = 1`. Every rotation orbit
-- is then a single tuple, so elements of `ZMod 3` with the same minimal polynomial are equal.
example (x y : ZMod 3) (h : minpoly (ZMod 3) x = minpoly (ZMod 3) y) : x = y := by
  have hβ : LinearIndependent (ZMod 3)
      (fun i : Fin 1 => (1 : ZMod 3) ^ (Fintype.card (ZMod 3) ^ (i : ℕ))) :=
    linearIndependent_unique_iff.mpr (by simp)
  obtain ⟨m, hm⟩ := (normalBasisMap_rotation_iff_conj (ZMod 3) (ZMod 3) 1
    (Module.finrank_self (ZMod 3)) 1 hβ ![x] ![y]).mpr (by simpa using h)
  simpa using (congrFun hm 0).symm
