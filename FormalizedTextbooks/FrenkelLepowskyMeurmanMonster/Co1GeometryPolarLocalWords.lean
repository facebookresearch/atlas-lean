/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalGeneration

/-! Cached finite original-word certificates for genuine local line transports. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Chronological positive words in the five genuine Conway generators. -/
def monsterCo1PolarLocalWord : List (Fin 5) → Co1
  | [] => 1
  | k :: w => monsterCo1PolarLocalWord w * monsterCo1FiveGenerator k

/-- A cached binary trace retains and checks each actual original generator transition. -/
def monsterCo1PolarLocalTrace : ℕ → List (Fin 5 × ℕ) → Prop
  | _, [] => True
  | v, (k, u) :: w =>
      omegaOrbitBinaryMatrices k *ᵥ co1IrreducibleBitVector v = co1IrreducibleBitVector u ∧
        monsterCo1PolarLocalTrace u w

/-- Recursive decidability computes only the individual cached transition checks. -/
def monsterCo1PolarLocalTraceDecidable : (v : ℕ) → (w : List (Fin 5 × ℕ)) →
    Decidable (monsterCo1PolarLocalTrace v w)
  | _, [] => isTrue trivial
  | v, (k, u) :: w => by
    change Decidable (_ ∧ monsterCo1PolarLocalTrace u w)
    letI := monsterCo1PolarLocalTraceDecidable u w
    infer_instance

instance (v : ℕ) (w : List (Fin 5 × ℕ)) : Decidable (monsterCo1PolarLocalTrace v w) :=
  monsterCo1PolarLocalTraceDecidable v w

/-- The five finite matrices act through the actual Conway generators. -/
theorem monsterCo1PolarLocal_generator_matrix (k : Fin 5) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (monsterCo1FiveGenerator k) v = omegaOrbitBinaryMatrices k *ᵥ v := by
  change leechBinaryAction (omegaOrbitIsometry k) v = _
  exact omegaOrbitIsometry_binary k v

/-- Every cached trace identifies the complete actual word action on its initial vector. -/
theorem monsterCo1PolarLocalTrace_sound (v : ℕ) (w : List (Fin 5 × ℕ))
    (h : monsterCo1PolarLocalTrace v w) :
    co1BinaryAction (monsterCo1PolarLocalWord (w.map Prod.fst))
      (co1IrreducibleBitVector v) =
        co1IrreducibleBitVector (w.foldl (fun _ s => s.2) v) := by
  induction w generalizing v with
  | nil => simp [monsterCo1PolarLocalWord]
  | cons s w ih =>
    rcases s with ⟨k, u⟩
    rcases h with ⟨hku, hw⟩
    simp only [List.map_cons, monsterCo1PolarLocalWord, map_mul,
      LinearEquiv.mul_apply, List.foldl_cons]
    rw [monsterCo1PolarLocal_generator_matrix, hku]
    exact ih u hw

/-- Integral basis coordinates for the genuine standard odd pentad. -/
def monsterCo1PolarPentadCoordinates : Fin 24 → ℤ :=
  ![1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The cached coordinates reconstruct the whole genuine pentad lattice vector. -/
theorem monsterCo1PolarPentadCoordinates_vector :
    leechExplicitCoordinateMap monsterCo1PolarPentadCoordinates = monsterCo1PolarPentadLattice := by
  apply Subtype.ext
  change leechBasisMatrix *ᵥ monsterCo1PolarPentadCoordinates =
    monsterCo1PolarPentadVector monsterCo1PolarStandardPentad
  decide +kernel

/-- The whole actual pentad geometry point has the stated complete binary coordinates. -/
theorem monsterCo1PolarPentadPoint_binary :
    monsterCo1PolarPentadPoint.val = co1IrreducibleBitVector 8450048 := by
  change leechHyperbolicCoordinates (leechReduction monsterCo1PolarPentadLattice) = _
  have hc : leechExplicitCoordinates monsterCo1PolarPentadLattice =
      monsterCo1PolarPentadCoordinates := by
    rw [← monsterCo1PolarPentadCoordinates_vector]
    exact leechExplicitCoordinates.apply_symm_apply _
  rw [leechHyperbolicCoordinates_explicit, hc]
  change leechHyperbolicInverse *ᵥ integerParity monsterCo1PolarPentadCoordinates = _
  decide +kernel

/-- The already proved genuine tetrad point has its literal complete binary vector. -/
theorem monsterCo1PolarLocal_tetrad_binary :
    monsterCo1GeometryTetradPoint.val = co1IrreducibleBitVector 4194304 := by
  change leechBinaryAction (omegaOrbitIsometry 0) monsterCo1GeometryBasePoint.val = _
  rw [monsterCo1GeometryBasePoint_binary, omegaOrbitIsometry_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
