/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorXiCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddQTensorFactors

/-! Exact complete rational tensor transport by genuine phase-preserving source frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The complete extraspecial rational signed translation. -/
def generatedAxisGlobalRationalTensorQ (q : Q) (T : GeneratedAxisGlobalRationalTensor)
    (k : Fin 4096) (i : Fin 24) : ℚ :=
  (generatedAxisGlobalIntSign (spinPhase q (golayLabelCoefficients k)) : ℚ) *
    T (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + spinTranslation q)) i

/-- Every original Q correction retains its full central phase in every physical coordinate. -/
theorem generatedAxisGlobalRationalTensorQ_actual (q : Q) (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (localFiberIncl q) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalRationalTensorQ q T) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [localFiberQ_tensor_columns]
  change qSign (spinPhase q (golayLabelCoefficients k)) *
    generatedAxisGlobalRationalTensorReal T (golayLabelCoefficients k + spinTranslation q) i = _
  simp only [generatedAxisGlobalRationalTensorQ, generatedAxisGlobalRationalTensorReal,
    generatedAxisGlobalSpinLabel_coeff, Rat.cast_mul, Rat.cast_intCast,
    generatedAxisGlobalIntSign_real]
  ring

/-- The seven original frame letters used in the complete Fourth comparison words. -/
def generatedAxisGlobalRationalFrameLetter : Fin 7 → Fin 10 := ![0, 1, 2, 6, 7, 8, 9]

/-- Every frame letter uses the whole original rational tensor operator. -/
def generatedAxisGlobalRationalTensorFrameLetter (l : Fin 7)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  match l.val with
  | 0 => generatedAxisGlobalRationalTensorXiCached T
  | 1 => generatedAxisGlobalRationalTensorXiCached (generatedAxisGlobalRationalTensorXiCached T)
  | 2 => generatedAxisGlobalRationalTensorSign 16 0 T
  | 3 => generatedAxisGlobalRationalTensorMonomial [(0, false)] T
  | 4 => generatedAxisGlobalRationalTensorMonomial [(0, true)] T
  | 5 => generatedAxisGlobalRationalTensorMonomial [(1, false)] T
  | _ => generatedAxisGlobalRationalTensorMonomial [(1, true)] T

/-- The complete real tensor action of every permitted actual source letter. -/
theorem generatedAxisGlobalRationalTensorFrameLetter_actual (l : Fin 7)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter
      (generatedAxisGlobalRationalFrameLetter l)) (generatedAxisGlobalRationalTensorReal T) =
    generatedAxisGlobalRationalTensorReal (generatedAxisGlobalRationalTensorFrameLetter l T) := by
  fin_cases l
  · exact generatedAxisGlobalRationalTensorXiCached_actual T
  · change localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal
        (generatedAxisGlobalRationalTensorXiCached (generatedAxisGlobalRationalTensorXiCached T))
    rw [generatedAxisGlobalOddSourceFiberLetter_one, map_mul, LinearEquiv.mul_apply]
    rw [show generatedAxisGlobalOddSourceFiberLetter 0 = xiSpinLocalFiber from rfl]
    rw [generatedAxisGlobalRationalTensorXiCached_actual,
      generatedAxisGlobalRationalTensorXiCached_actual]
  · exact generatedAxisGlobalRationalTensorSign_actual T 16 0
  · change localTensorRepresentation (([(0, false)].map
      generatedFourthMonomialFiberLetter).prod) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal
        (generatedAxisGlobalRationalTensorMonomial [(0, false)] T)
    exact generatedAxisGlobalRationalTensorMonomial_actual T [(0, false)]
  · change localTensorRepresentation (([(0, true)].map
      generatedFourthMonomialFiberLetter).prod) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal
        (generatedAxisGlobalRationalTensorMonomial [(0, true)] T)
    exact generatedAxisGlobalRationalTensorMonomial_actual T [(0, true)]
  · change localTensorRepresentation (([(1, false)].map
      generatedFourthMonomialFiberLetter).prod) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal
        (generatedAxisGlobalRationalTensorMonomial [(1, false)] T)
    exact generatedAxisGlobalRationalTensorMonomial_actual T [(1, false)]
  · change localTensorRepresentation (([(1, true)].map
      generatedFourthMonomialFiberLetter).prod) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal
        (generatedAxisGlobalRationalTensorMonomial [(1, true)] T)
    exact generatedAxisGlobalRationalTensorMonomial_actual T [(1, true)]

/-- Product-order words apply the rightmost original letter first. -/
def generatedAxisGlobalRationalTensorFrameWord : List (Fin 7) →
    GeneratedAxisGlobalRationalTensor → GeneratedAxisGlobalRationalTensor
  | [], T => T
  | l :: ls, T => generatedAxisGlobalRationalTensorFrameLetter l
      (generatedAxisGlobalRationalTensorFrameWord ls T)

/-- Every rational frame word binds all physical coefficients to its genuine original fiber. -/
theorem generatedAxisGlobalRationalTensorFrameWord_actual (ls : List (Fin 7))
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation
      ((ls.map (fun l => generatedAxisGlobalOddSourceFiberLetter
        (generatedAxisGlobalRationalFrameLetter l))).prod)
      (generatedAxisGlobalRationalTensorReal T) =
    generatedAxisGlobalRationalTensorReal (generatedAxisGlobalRationalTensorFrameWord ls T) := by
  induction ls with
  | nil => simp [generatedAxisGlobalRationalTensorFrameWord]
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, map_mul]
    rw [LinearEquiv.mul_apply, ih, generatedAxisGlobalRationalTensorFrameLetter_actual]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
