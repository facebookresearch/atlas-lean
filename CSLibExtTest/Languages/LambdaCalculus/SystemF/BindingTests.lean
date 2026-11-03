/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.SystemF.Semantics

/-! # Two-sort binding and safety regression probes -/

open Cslib.Languages.LambdaCalculus.SystemF

private def idType : Ty 0 := .all (.arr (.var 0) (.var 0))

private def polyId : Tm 0 0 := .tabs (.lam (.var 0) (.var 0))

-- No assumptions: the pure polymorphic identity has its impredicative type.
example : Typing Fin.elim0 polyId idType := .tabs (.lam (.var 0))

-- Substituting a free type under forall must not capture it.
example :
    Ty.instantiate (.all (.arr (.var 0) (.var 1)) : Ty 3) (.var 1) =
      .all (.arr (.var 0) (.var 2)) := rfl

-- Two nested quantifiers preserve both bound variables during instantiation.
example : Ty.instantiate
    (.all (.all (.arr (.var 2) (.var 0))) : Ty 1) idType =
      .all (.all (.arr (.all (.arr (.var 0) (.var 0))) (.var 0))) := rfl

-- A type lambda weakens the inserted term's type, not its term indices.
example : Tm.instantiate (.tabs (.var 0) : Tm 1 1)
    (.lam (.var 0) (.var 0)) =
      .tabs (.lam (.var 1) (.var 0)) := rfl

-- A term lambda must shift a free argument to avoid capturing it.
example : Tm.instantiate (.lam (.var 0) (.var 1) : Tm 1 2) (.var 0) =
    .lam (.var 0) (.var 1) := rfl

-- Self-application at a type variable is rejected by the actual typing rules.
example (A : Ty 1) :
    ¬ Typing (fun _ : Fin 1 => Ty.var 0) (.app (.var 0) (.var 0)) A := by
  intro h
  cases h with
  | app hf ha => cases hf

-- Instantiation at another quantified type exercises impredicativity.
example : Typing Fin.elim0 (.tapp polyId idType) (.arr idType idType) :=
  .tapp (.tabs (.lam (.var 0)))

-- The real closed CBV input takes a type-beta step and then a term-beta step.
example : Steps (.app (.tapp polyId idType) polyId) polyId :=
  (Relation.ReflTransGen.single (.appFun .tyBeta)).tail (.beta .tabs)
