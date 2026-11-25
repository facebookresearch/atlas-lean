/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.KuratowskiClosureComplement

open Set
open Topology.ClosureCompl
open MathlibExt.Topology.KuratowskiClosureComplement

/-- Discrete topology on `Fin 2` for the concrete examples below. -/
local instance : TopologicalSpace (Fin 2) where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

/-- Mathlib's canonical obtainability predicate contains its seed set. -/
example : IsObtainable ({0} : Set (Fin 2)) {0} :=
  .base

/-- The canonical predicate is closed under complement. -/
example : IsObtainable ({0} : Set (Fin 2)) ({0}ᶜ) :=
  .complement .base

/-- The canonical predicate is closed under closure. -/
example : IsObtainable ({0} : Set (Fin 2)) (closure {0}) :=
  .closure .base

/-- The canonical fourteen forms characterize obtainability. -/
example : ({0} : Set (Fin 2)) ∈ theFourteen {0} ↔
    IsObtainable ({0} : Set (Fin 2)) {0} :=
  mem_theFourteen_iff_isObtainable

/-- Mathlib's direct numerical bound is available. -/
example : {t : Set (Fin 2) | IsObtainable ({0} : Set (Fin 2)) t}.ncard ≤ 14 :=
  ncard_isObtainable_le_fourteen _

/-- The finite-and-cardinality wrapper holds on a concrete space and set. -/
example : {t : Set (Fin 2) | IsObtainable ({0} : Set (Fin 2)) t}.Finite ∧
    {t : Set (Fin 2) | IsObtainable ({0} : Set (Fin 2)) t}.ncard ≤ 14 :=
  kuratowski_closure_complement _
