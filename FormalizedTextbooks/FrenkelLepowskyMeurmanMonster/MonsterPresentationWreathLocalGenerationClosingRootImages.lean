/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine diagonal images of the closing-root words under an eventual source homomorphism. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationWreathLocalGenerationClosingRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555ActualWreathGeneration
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

variable {M : Type*} [Group M]

/-- Read the first factor of the image of closingRoot times the central generator. -/
def monsterWreathClosingDiagonal (f : BimonsterPresentation →* M ≀ᵣ WreathParity)
    (i : Fin 3) : M := (f (monsterWreathClosingRoot i * PresentedGroup.of none)).left 1

/-- Commuting with swap and having even parity forces the word image to be a true diagonal. -/
theorem monsterWreathClosingDiagonal_word (f : BimonsterPresentation →* M ≀ᵣ WreathParity)
    (hf : f (PresentedGroup.of none) = wreathSwap M) (i : Fin 3) :
    f (monsterWreathClosingRoot i * PresentedGroup.of none) =
      y555WreathBase (monsterWreathClosingDiagonal f i, monsterWreathClosingDiagonal f i) := by
  have hp : RegularWreathProduct.rightHom.comp f = bimonsterParity :=
    y555_parity_eq _ (by change (f (PresentedGroup.of none)).right = _; rw [hf]; rfl)
  have hr : (f (monsterWreathClosingRoot i * PresentedGroup.of none)).right = 1 := by
    change (RegularWreathProduct.rightHom.comp f) _ = 1
    rw [hp]
    exact y555A11ClosingRoot_center_parity _ _
  have hc : Commute (f (monsterWreathClosingRoot i)) (wreathSwap M) := by
    simpa only [hf] using (monsterWreathClosingRoot_commute_center i).map f
  have hcc : f (monsterWreathClosingRoot i * PresentedGroup.of none) ∈
      wreathSwapCentralizer M := by
    rw [map_mul, hf]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hc.mul_left (Commute.refl (wreathSwap M))).eq
  have hl := (mem_wreathSwapCentralizer_iff M _).mp hcc
  apply RegularWreathProduct.ext
  · funext x
    simp only [y555WreathBase, monsterWreathClosingDiagonal, MonoidHom.coe_mk,
      OneHom.coe_mk, hl x, ite_self]
  · exact hr

/-- A subgroup containing every source-generator image contains every closing diagonal word. -/
theorem monsterWreathClosingDiagonal_mem (f : BimonsterPresentation →* M ≀ᵣ WreathParity)
    (hf : f (PresentedGroup.of none) = wreathSwap M) (K : Subgroup (M ≀ᵣ WreathParity))
    (hK : ∀ v : Y555Vertex, f (PresentedGroup.of v) ∈ K) (i : Fin 3) :
    y555WreathBase (monsterWreathClosingDiagonal f i, monsterWreathClosingDiagonal f i) ∈ K := by
  rw [← monsterWreathClosingDiagonal_word f hf i, map_mul]
  apply K.mul_mem
  · change f ((List.map (fun v => (PresentedGroup.of v : BimonsterPresentation))
      (y555A11ClosingWord (monsterWreathClosingArms i).1
        (monsterWreathClosingArms i).2)).prod) ∈ K
    generalize y555A11ClosingWord (monsterWreathClosingArms i).1
      (monsterWreathClosingArms i).2 = w
    induction w with
    | nil => simpa only [List.map_nil, List.prod_nil, map_one] using K.one_mem
    | cons v w ih =>
      simp only [List.map_cons, List.prod_cons, map_mul]
      exact K.mul_mem (hK v) ih
  · exact hK none

/-- Once the literal candidate homomorphism is proved, the three actual diagonal words
belong to the actual Norton-generated wreath subgroup. No homomorphism is assumed to exist. -/
theorem monsterNortonClosingDiagonal_mem
    (f : BimonsterPresentation →* G ≀ᵣ WreathParity)
    (hf : ∀ v : Y555Vertex, f (PresentedGroup.of v) = y555NortonActualCandidate v) (i : Fin 3) :
    y555WreathBase (monsterWreathClosingDiagonal f i, monsterWreathClosingDiagonal f i) ∈
      y555NortonActualGeneratedWreath := by
  apply monsterWreathClosingDiagonal_mem f
    ((hf none).trans y555NortonActualCandidate_center)
  intro v
  rw [hf v]
  exact Subgroup.subset_closure ⟨v, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
