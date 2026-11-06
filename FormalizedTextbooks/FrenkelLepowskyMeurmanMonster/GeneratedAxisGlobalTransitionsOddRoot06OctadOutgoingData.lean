/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSparseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseBinding

/-! Exact original source families for the remaining root-six positive octad transition. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- All original octads occurring in this source and its complete outgoing short support. -/
def generatedAxisGlobalOddRoot06ActiveOctad : Fin 15 → Fin 759 :=
  ![0, 7, 28, 29, 30, 31, 243, 244, 248, 249, 510, 624, 625, 627, 628]

/-- Only the listed original octads can occur in this complete source packet. -/
def generatedAxisGlobalOddRoot06InitialAllowed : GriessShortIndex → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl (o, _)) => ∃ k : Fin 15, generatedAxisGlobalOddRoot06ActiveOctad k = o
  | Sum.inr (Sum.inr _) => False

/-- The exact finite original family restriction is decidable.
-/
instance generatedAxisGlobalOddRoot06InitialAllowedDecidable (r : GriessShortIndex) :
    Decidable (generatedAxisGlobalOddRoot06InitialAllowed r) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩) <;>
    unfold generatedAxisGlobalOddRoot06InitialAllowed <;> infer_instance

/-- The listed original octads are the only allowed octad indices in an outgoing label. -/
def generatedAxisGlobalOddRoot06OctadAllowed : GriessShortIndex → Prop
  | Sum.inr (Sum.inl (o, _)) => ∃ k : Fin 15, generatedAxisGlobalOddRoot06ActiveOctad k = o
  | _ => True

/-- The exact finite original outgoing octad restriction is decidable. -/
instance generatedAxisGlobalOddRoot06OctadAllowedDecidable (r : GriessShortIndex) :
    Decidable (generatedAxisGlobalOddRoot06OctadAllowed r) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩) <;>
    unfold generatedAxisGlobalOddRoot06OctadAllowed <;> infer_instance

/-- The complete outgoing short packet is the original rational source triality formula. -/
def generatedAxisGlobalOddRoot06PositiveShortQ : GriessShortIndex → ℚ :=
  (generatedAxisGlobalRationalTriality (generatedAxisGlobalOddSparseRootPacket 1)).2.1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
