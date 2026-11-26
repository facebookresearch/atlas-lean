/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ModelTheory.RealClosedFieldQE

namespace MathlibExt.TheoryOfComputation.RealClosedFieldQEWanted
namespace ProgramVerification.RealClosedFieldQE

-- In two extended environments, the outer free variable has moved to index two.
example (env : Nat → ℝ) (x y : ℝ) :
    (Term.add (.mul (.var 0) (.var 1)) (.neg (.var 2))).eval (cons y (cons x env)) =
      y * x + -(env 0) := rfl

-- Zero is included, even when the next free variable is negative.
example :
    (Formula.ex (.eq (.mul (.var 0) (.var 0)) (.var 1))).Holds (cons 0 (fun _ => -1)) := by
  apply (holds_ex_sq _).2
  simp [Formula.not, Formula.Holds, Term.eval, cons]

-- A square in the tail of the environment cannot make the negative head a square.
example :
    ¬ (Formula.ex (.eq (.mul (.var 0) (.var 0)) (.var 1))).Holds (cons (-1) (fun _ => 4)) := by
  intro h
  apply (holds_ex_sq _).1 h
  simp [Formula.Holds, Term.eval, cons]

-- Eliminating the existential yields a syntactically quantifier-free formula.
example : (Formula.not (.lt (.var 0) (.const 0))).IsQF := ⟨trivial, trivial⟩

end ProgramVerification.RealClosedFieldQE
end MathlibExt.TheoryOfComputation.RealClosedFieldQEWanted
