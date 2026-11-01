/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact abstract A11 closing-root words in the full independent Y555 presentation. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Presentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555TypeAParabolicOrderReflection
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The eleven-vertex path from the end of arm a to the end of arm b. -/
def y555A11Path (a b : Fin 3) (i : Fin 11) : Y555Vertex :=
  if h : i.val < 5 then some (a, ⟨4 - i.val, by omega⟩)
  else if i.val = 5 then none
  else some (b, ⟨i.val - 6, by omega⟩)

/-- The two-arm path has exactly the adjacency relation of an eleven-vertex chain. -/
theorem y555A11Path_adjacent (a b : Fin 3) (hab : a ≠ b) (i j : Fin 11) :
    y555Adjacent (y555A11Path a b i) (y555A11Path a b j) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  fin_cases a <;> fin_cases b <;> norm_num at hab
  all_goals fin_cases i <;> fin_cases j <;> decide +kernel

/-- Distinct positions on the two-arm path give distinct source generators. -/
theorem y555A11Path_injective (a b : Fin 3) (hab : a ≠ b) :
    Function.Injective (y555A11Path a b) := by
  intro i j hij
  fin_cases a <;> fin_cases b <;> norm_num at hab
  all_goals fin_cases i <;> fin_cases j <;> simp_all [y555A11Path]

/-- Natural-number indexing of the eleven simple generators, extended by ones. -/
def y555A11Generators (a b : Fin 3) (i : ℕ) : BimonsterPresentation :=
  if h : i < 11 then PresentedGroup.of (y555A11Path a b ⟨i, h⟩) else 1

private theorem y555_generator_mul_self (v : Y555Vertex) :
    (PresentedGroup.of v : BimonsterPresentation) * PresentedGroup.of v = 1 := by
  simpa only [pow_two] using y555_generator_sq v

private theorem y555_generator_inverse (v : Y555Vertex) :
    (PresentedGroup.of v : BimonsterPresentation)⁻¹ = PresentedGroup.of v :=
  inv_eq_of_mul_eq_one_right (y555_generator_mul_self v)

private theorem y555_generators_commute (u v : Y555Vertex) (huv : u ≠ v)
    (ha : ¬ y555Adjacent u v) :
    (PresentedGroup.of u : BimonsterPresentation) * PresentedGroup.of v =
      PresentedGroup.of v * PresentedGroup.of u := by
  have h := y555_coxeter_relation u v huv
  simp only [ha, ↓reduceIte, pow_two] at h
  have hi := eq_inv_of_mul_eq_one_left h
  simpa only [mul_inv_rev, y555_generator_inverse] using hi

private theorem y555_generators_braid (u v : Y555Vertex) (huv : u ≠ v)
    (ha : y555Adjacent u v) :
    (PresentedGroup.of u : BimonsterPresentation) * PresentedGroup.of v * PresentedGroup.of u =
      PresentedGroup.of v * PresentedGroup.of u * PresentedGroup.of v := by
  have h := y555_coxeter_relation u v huv
  simp only [ha, ↓reduceIte, pow_succ, pow_zero, one_mul] at h
  have hi := congrArg (fun x => x * (PresentedGroup.of v : BimonsterPresentation))
    (eq_inv_of_mul_eq_one_left h)
  simpa only [mul_inv_rev, y555_generator_inverse, mul_assoc,
    y555_generator_mul_self, mul_one] using hi

/-- The actual defining relations of the independent presentation make this path type A11. -/
theorem y555A11Chain_relations (a b : Fin 3) (hab : a ≠ b) :
    TypeAChainRelations (y555A11Generators a b) 11 where
  square i hi := by
    simp only [y555A11Generators, dite_eq_left hi]
    exact y555_generator_mul_self _
  commute i j hi hj hij := by
    simp only [y555A11Generators, dite_eq_left hi, dite_eq_left hj]
    apply y555_generators_commute
    · intro he
      have he' := y555A11Path_injective a b hab he
      have heval := congrArg Fin.val he'
      dsimp only at heval
      omega
    · rw [y555A11Path_adjacent a b hab]
      dsimp only
      omega
  braid i hi := by
    have hi' : i < 11 := by omega
    simp only [y555A11Generators, dite_eq_left hi, dite_eq_left hi']
    apply y555_generators_braid
    · intro he
      have he' := y555A11Path_injective a b hab he
      have heval := congrArg Fin.val he'
      dsimp only at heval
      omega
    · rw [y555A11Path_adjacent a b hab]
      exact Or.inl rfl

/-- The literal 21-letter closing-root word of the two-arm A11 path. -/
def y555A11ClosingWord (a b : Fin 3) : List Y555Vertex :=
  [some (a, 4), some (a, 3), some (a, 2), some (a, 1), some (a, 0), none,
    some (b, 0), some (b, 1), some (b, 2), some (b, 3), some (b, 4),
    some (b, 3), some (b, 2), some (b, 1), some (b, 0), none,
    some (a, 0), some (a, 1), some (a, 2), some (a, 3), some (a, 4)]

/-- Evaluate the literal closing-root word in the independent full Y555 presentation. -/
def y555A11ClosingRoot (a b : Fin 3) : BimonsterPresentation :=
  ((y555A11ClosingWord a b).map fun v => (PresentedGroup.of v : BimonsterPresentation)).prod

/-- The literal word is exactly the closing reflection from the insertion calculus. -/
theorem y555A11ClosingRoot_eq_reflection (a b : Fin 3) :
    y555A11ClosingRoot a b = typeAClosingReflection (y555A11Generators a b) 10 := by
  simp [y555A11ClosingRoot, y555A11ClosingWord, typeAClosingReflection, typeAInsertion,
    y555A11Generators, y555A11Path, mul_inv_rev, y555_generator_inverse, mul_assoc]

/-- Every closing-root word is an involution in the independent presentation. -/
theorem y555A11ClosingRoot_square (a b : Fin 3) (hab : a ≠ b) :
    y555A11ClosingRoot a b * y555A11ClosingRoot a b = 1 := by
  rw [y555A11ClosingRoot_eq_reflection]
  exact typeAClosingReflection_square (y555A11Chain_relations a b hab)

/-- Every closing-root word commutes with the distinguished central source generator. -/
theorem y555A11ClosingRoot_commute_center (a b : Fin 3) (hab : a ≠ b) :
    Commute (y555A11ClosingRoot a b) (PresentedGroup.of none) := by
  rw [y555A11ClosingRoot_eq_reflection]
  simpa [y555A11Generators, y555A11Path] using
    typeAClosingReflection_commute_interior (y555A11Chain_relations a b hab) 5
      (by omega) (by omega)

/-- The closing root has the same odd presentation parity as a simple reflection. -/
theorem y555A11ClosingRoot_parity (a b : Fin 3) :
    bimonsterParity (y555A11ClosingRoot a b) = Multiplicative.ofAdd (1 : ZMod 2) := by
  rw [y555A11ClosingRoot_eq_reflection, typeAClosingReflection, map_mul, map_mul, map_inv]
  have hg : bimonsterParity (y555A11Generators a b 10) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
    simp [y555A11Generators, bimonsterParity_generator]
  rw [hg]
  rw [mul_comm _ (Multiplicative.ofAdd (1 : ZMod 2)), mul_assoc,
    inv_mul_cancel, mul_one]

/-- Multiplying the closing root by the central generator gives an even word centralizing it. -/
theorem y555A11ClosingRoot_center_parity (a b : Fin 3) :
    bimonsterParity (y555A11ClosingRoot a b * (PresentedGroup.of none)) = 1 := by
  rw [map_mul, y555A11ClosingRoot_parity, bimonsterParity_generator]
  decide +kernel

/-- The three two-arm paths, oriented to give the source closing-root words
associated with the missing point labels 10,12,3. No actual-Q identification is assumed. -/
def monsterWreathClosingArms : Fin 3 → Fin 3 × Fin 3 := ![(1, 0), (2, 0), (2, 1)]

/-- The three exact 21-letter word witnesses in the independent presentation. -/
def monsterWreathClosingWord (i : Fin 3) : List Y555Vertex :=
  y555A11ClosingWord (monsterWreathClosingArms i).1 (monsterWreathClosingArms i).2

/-- Each of the three literal witnesses has exactly twenty-one source letters. -/
theorem monsterWreathClosingWord_length (i : Fin 3) :
    (monsterWreathClosingWord i).length = 21 := by
  fin_cases i <;> rfl

/-- Evaluate the three literal closing-root witnesses in the independent presentation. -/
def monsterWreathClosingRoot (i : Fin 3) : BimonsterPresentation :=
  y555A11ClosingRoot (monsterWreathClosingArms i).1 (monsterWreathClosingArms i).2

/-- Each of the three exact source word witnesses is an involution. -/
theorem monsterWreathClosingRoot_square (i : Fin 3) :
    monsterWreathClosingRoot i * monsterWreathClosingRoot i = 1 := by
  apply y555A11ClosingRoot_square
  fin_cases i <;> decide +kernel

/-- Each exact source word witness commutes with the distinguished central generator. -/
theorem monsterWreathClosingRoot_commute_center (i : Fin 3) :
    Commute (monsterWreathClosingRoot i) (PresentedGroup.of none) := by
  apply y555A11ClosingRoot_commute_center
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
