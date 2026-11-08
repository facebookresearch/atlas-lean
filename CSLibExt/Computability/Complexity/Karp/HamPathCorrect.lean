/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathForward
public import CSLibExt.Computability.Complexity.Karp.HamPathNormal
public import CSLibExt.Computability.Complexity.PathCorrect
public import CSLibExt.Computability.Complexity.DenseToBinary

/-!
# Correctness of Karp's reduction SAT ≤ HAMPATH

`satDec_eq_hamPathDec_reduceHam`: Sipser's construction `reduceHam` (`Karp.HamPath`) preserves
membership. The construction has a Hamiltonian path iff the formula is satisfiable
(`exists_isHamPath_iff_cnfSat`): forward by `exists_isHamPath_of_cnfSat`, backward by the
separator argument `detoursNormal_of_isHamPath` and `cnfSat_of_isHamPath`. Undecodable inputs go to
`noHam`, a no-instance (`hamPathDec_noHam`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-- **The construction has a Hamiltonian path iff the formula is satisfiable.** -/
theorem exists_isHamPath_iff_cnfSat (φ : CNF) :
    (∃ p, IsHamPath (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)
      (hpT φ.length 0) (hpT φ.length (hamVars φ).length) p) ↔ CNFSat φ :=
  ⟨fun ⟨_, hp⟩ => cnfSat_of_isHamPath hp (detoursNormal_of_isHamPath hp),
    exists_isHamPath_of_cnfSat⟩

/-- `hamPathDec` on an encoded instance. -/
theorem hamPathDec_encodeP (s t n : ℕ) (es : List (ℕ × ℕ)) :
    hamPathDec (Path.encodeP s t n es) = true ↔ ∃ p, IsHamPath n es s t p := by
  classical
  unfold hamPathDec
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨s', t', n', es', he, hp⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Path.encodeP_inj he
    exact hp
  · exact fun hp => ⟨s, t, n, es, rfl, hp⟩

/-- `noHam` is a no-instance: a path from `0` to `0` through two vertices repeats `0`. -/
theorem hamPathDec_noHam : hamPathDec noHam = false := by
  rw [Bool.eq_false_iff, ne_eq, noHam, hamPathDec_encodeP]
  rintro ⟨p, hnd, hlen, -, hhd, hlast, -⟩
  match p, hlen with
  | [a, b], _ =>
      simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons,
        List.getLast?_singleton] at hhd hlast
      subst hhd hlast
      simp at hnd

/-- **SAT ≤ HAMPATH preserves membership.** -/
theorem satDec_eq_hamPathDec_reduceHam (x : List Bool) : satDec x = hamPathDec (reduceHam x) := by
  unfold reduceHam
  split
  next φ h =>
    rw [decodeCNF_eq_some_iff] at h
    subst h
    rw [Bool.eq_iff_iff, DenseSAT.ToBinary.satDec_encodeCNF, toHam, hamPathDec_encodeP,
      exists_isHamPath_iff_cnfSat]
  next h => rw [DenseSAT.ToBinary.satDec_of_decodeCNF_eq_none h, hamPathDec_noHam]

end Cslib.Complexity.Karp
