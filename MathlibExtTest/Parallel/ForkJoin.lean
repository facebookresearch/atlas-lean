/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Parallel.ForkJoin

@[expose] public section

/-- Computation: work and span of a small fork-join program. -/
example : (Prog.par Prog.task (Prog.seq Prog.task Prog.task)).work = 3 ∧
    (Prog.par Prog.task (Prog.seq Prog.task Prog.task)).span = 2 :=
  ⟨rfl, rfl⟩
