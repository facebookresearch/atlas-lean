/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.PathCorrect
public import CSLibExt.Computability.Complexity.PathMachine
public import CSLibExt.Computability.Complexity.Host

/-!
# PATH ∈ P

Sipser, Theorem 7.14, on the canonical classes: the marking machine `Path.Machine` in the decider
host (`Host.isPolyTime_decider`) computes `pathCheck` in polynomial time
(`isPolyTime_pathCheck`), and `pathCheck` decides PATH (`pathDec_eq_pathCheck`), so
`pathDec ∈ P` (`pathDec_mem_P`).
-/

@[expose] public section

namespace Cslib.Complexity.Path

open MetaMathlibExt.ComplexityTheory

instance Machine.instFintypeΓ (k : Machine.K) : Fintype (Machine.Γ k) := by
  cases k <;> infer_instance

/-- The marking machine as a host component. -/
abbrev pathComp : Host.Comp where
  K := Machine.K
  Γ := Machine.Γ
  L := Machine.Lab
  prog := Machine.prog
  ks := [.X, .O, .E, .J, .S, .T, .N, .U, .V, .M, .P]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **The marking algorithm is polynomial-time.** -/
theorem isPolyTime_pathCheck : IsPolyTime pathCheck :=
  Host.isPolyTime_decider (c := pathComp) (cX := Machine.K.X) (cO := Machine.K.O)
    (gX := SatVerifier.Sym.bit) (start := Machine.start) (done := Machine.Lab.done)
    (Equiv.refl Bool) pathCheck (Polynomial.C 8 * (Polynomial.X + 1) ^ 4) rfl fun x => by
      obtain ⟨v', S', r, h⟩ := Machine.run x false (Function.update (fun _ => [])
        Machine.K.X (x.map SatVerifier.Sym.bit)) (by simp) (fun k hk => by simp [hk])
      exact ⟨v', S', r.mono (le_of_eq (by simp)), by simpa using h⟩

/-- **PATH ∈ P** (Sipser, Theorem 7.14). -/
theorem pathDec_mem_P : pathDec ∈ P := by
  show IsPolyTime pathDec
  rw [show pathDec = pathCheck from funext pathDec_eq_pathCheck]
  exact isPolyTime_pathCheck

end Cslib.Complexity.Path
