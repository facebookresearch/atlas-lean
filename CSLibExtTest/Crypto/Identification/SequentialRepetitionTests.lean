/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.GraphIsomorphism

/-!
# Tests for sequential repetition of Sigma protocols

`allAccept` unfolds round by round: zero rounds are always accepted, and one round is accepted
exactly when the single transcript is. For the graph-isomorphism protocol on the empty and the
complete graph on `Fin 2` (no witness), a prover that always answers with the identity is
accepted on at most one challenge sequence, and the generic bound `1 / |Ch| ^ m` specializes to
`1 / 2 ^ m`.
-/

@[expose] public section

namespace Cslib.Crypto.SequentialRepetitionTests

open Cslib.Crypto.Identification Cslib.Crypto.Identification.GraphIsomorphism Cslib.Crypto.Framework

example {X W K Cm Ch Z : Type} (P : SigmaProtocol X W K Cm Ch Z) (x : X) (a : List Ch → Cm)
    (z : List Ch → Ch → Z) (c : Fin 0 → Ch) : P.allAccept x a z 0 c = true := rfl

example {X W K Cm Ch Z : Type} (P : SigmaProtocol X W K Cm Ch Z) (x : X) (a : List Ch → Cm)
    (z : List Ch → Ch → Z) (c : Fin 1 → Ch) :
    P.allAccept x a z 1 c = P.verify x (a []) (c 0) (z [] (c 0)) := by
  simp [SigmaProtocol.allAccept]

/-- The empty and the complete graph on two vertices are not isomorphic. -/
theorem not_iso : IsEmpty ((⊥ : SimpleGraph (Fin 2)) ≃g (⊤ : SimpleGraph (Fin 2))) := by
  refine ⟨fun e => ?_⟩
  have h : (⊤ : SimpleGraph (Fin 2)).Adj (e 0) (e 1) := by simp
  exact (e.map_rel_iff.mp h).elim

example (m : ℕ) (c c' : Fin m → Bool)
    (h : (sigma (V := Fin 2)).allAccept (⊥, ⊤) (fun _ => ⊥) (fun _ _ => 1) m c = true)
    (h' : (sigma (V := Fin 2)).allAccept (⊥, ⊤) (fun _ => ⊥) (fun _ _ => 1) m c' = true) : c = c' :=
  sigma.allAccept_subsingleton sigma_specialSound
    (forall_not_rel_of_isEmpty not_iso) m _ _ c c' h h'

example (m : ℕ) :
    winProb ((sigma (V := Fin 2)).seqCheatGame (R := Unit) (⊥, ⊤) (fun _ _ => ⊥)
      (fun _ _ _ => 1) m) ≤ 1 / (Fintype.card Bool : ℝ) ^ m :=
  (sigma (V := Fin 2)).winProb_seqCheatGame_le sigma_specialSound
    (forall_not_rel_of_isEmpty not_iso) _ _ m

end Cslib.Crypto.SequentialRepetitionTests
