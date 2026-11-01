/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGenericRootImageLower
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixFixerCounting
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpatialProjection

/-! Attaining the original root and kernel Conway classes gives the complete actual lower count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Genuine Conway projection restricted to the entire original matrix section stabilizer. -/
def generatedTwelfthMatrixConwayProjection : generatedTwelfthMatrixSectionStabilizer →* Co1 :=
  (QuotientGroup.mk' signsSubgroup).comp
    (leechSeventhE8SectionGroup.subtype.comp generatedTwelfthMatrixSectionStabilizer.subtype)

/-- Only whole original matrix section elements whose Conway value is genuinely attained are kept. -/
def generatedTwelfthProjectionPreimage (P : Subgroup Co1) :
    Subgroup generatedTwelfthMatrixSectionStabilizer := P.comap generatedTwelfthMatrixConwayProjection

/-- The genuine original root action of the projection preimage. -/
def generatedTwelfthProjectionRootAction (P : Subgroup Co1) :
    generatedTwelfthProjectionPreimage P →* Equiv.Perm (Fin 120) :=
  generatedTwelfthMatrixRootAction.comp (generatedTwelfthProjectionPreimage P).subtype

/-- An original complete root generator whose genuine Conway value is attained. -/
def generatedTwelfthProjectionRootGenerator (P : Subgroup Co1)
    (hroot : ∀ g : Fin 3, (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) ∈ P)
    (g : Fin 3) : generatedTwelfthProjectionPreimage P :=
  ⟨generatedTwelfthMatrixRootGenerator g, hroot g⟩

/-- Original positive or inverse root letters retain actual attained Conway values. -/
def generatedTwelfthProjectionRootLetter (P : Subgroup Co1)
    (hroot : ∀ g : Fin 3, (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) ∈ P)
    (l : Fin 3 × Bool) : generatedTwelfthProjectionPreimage P :=
  if l.2 then (generatedTwelfthProjectionRootGenerator P hroot l.1)⁻¹
  else generatedTwelfthProjectionRootGenerator P hroot l.1

/-- Every original complete root letter retains its already proved genuine root action. -/
theorem generatedTwelfth_projection_root_letter_actual (P : Subgroup Co1)
    (hroot : ∀ g : Fin 3, (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) ∈ P)
    (l : Fin 3 × Bool) (r : Fin 120) :
    generatedTwelfthProjectionRootAction P (generatedTwelfthProjectionRootLetter P hroot l) r =
      generatedTwelfthMatrixFixerRootFiniteLetter l r := by
  change generatedTwelfthMatrixRootAction (generatedTwelfthProjectionRootLetter P hroot l).val r = _
  have hv : (generatedTwelfthProjectionRootLetter P hroot l).val =
      generatedTwelfthMatrixRootLetter l := by
    rcases l with ⟨g, b⟩
    cases b <;> rfl
  rw [hv]
  exact generatedTwelfth_matrix_root_letter_actual l r

/-- Every complete original witness word retains its actual root action in the projection preimage. -/
theorem generatedTwelfth_projection_root_word_actual (P : Subgroup Co1)
    (hroot : ∀ g : Fin 3, (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) ∈ P)
    (w : List (Fin 3 × Bool)) (r : Fin 120) :
    generatedTwelfthProjectionRootAction P
      ((w.map (generatedTwelfthProjectionRootLetter P hroot)).prod) r =
      w.foldr generatedTwelfthMatrixFixerRootFiniteLetter r := by
  induction w generalizing r with
  | nil => rw [List.map_nil, List.prod_nil, map_one]; rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, map_mul]
    change generatedTwelfthProjectionRootAction P (generatedTwelfthProjectionRootLetter P hroot l)
      (generatedTwelfthProjectionRootAction P
        ((w.map (generatedTwelfthProjectionRootLetter P hroot)).prod) r) = _
    rw [ih, generatedTwelfth_projection_root_letter_actual]
    rfl

/-- Each unchanged original root witness is a genuine element with an attained Conway class. -/
def generatedTwelfthProjectionRootWitness (P : Subgroup Co1)
    (hroot : ∀ g : Fin 3, (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) ∈ P)
    (n : Fin 86) : generatedTwelfthProjectionPreimage P :=
  ((generatedTwelfthMatrixFixerRootWitnessWord n).map
    (generatedTwelfthProjectionRootLetter P hroot)).prod

/-- Every original kernel element is retained as a genuine projection-preimage root kernel element. -/
def generatedTwelfthProjectionKernelEnumeration (P : Subgroup Co1)
    (hkernel : ∀ (b : Bool) (a : Fin 32) (p : Fin 16),
      (QuotientGroup.mk (generatedTwelfthRootKernelMonomial b a p) : Co1) ∈ P)
    (x : Bool × Fin 32 × Fin 16) : (generatedTwelfthProjectionRootAction P).ker :=
  let g := generatedTwelfthRootKernelEnumeration x
  ⟨⟨⟨g.val, generatedTwelfth_root_action_kernel_actual_matrix g⟩,
    hkernel x.1 x.2.1 x.2.2⟩, g.property⟩

/-- The entire original kernel remains injective in its actual physical coordinates. -/
theorem generatedTwelfth_projection_kernel_enumeration_injective (P : Subgroup Co1)
    (hkernel : ∀ (b : Bool) (a : Fin 32) (p : Fin 16),
      (QuotientGroup.mk (generatedTwelfthRootKernelMonomial b a p) : Co1) ∈ P) :
    Function.Injective (generatedTwelfthProjectionKernelEnumeration P hkernel) := by
  intro x y h
  apply generatedTwelfth_root_kernel_monomial_injective
  exact congrArg (fun k : (generatedTwelfthProjectionRootAction P).ker => k.val.val.val.val) h

/-- Attaining every original root and kernel projection forces at least 7,372,800 preimage elements. -/
theorem generatedTwelfth_projection_preimage_lower (P : Subgroup Co1)
    (hroot : ∀ g : Fin 3, (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) ∈ P)
    (hkernel : ∀ (b : Bool) (a : Fin 32) (p : Fin 16),
      (QuotientGroup.mk (generatedTwelfthRootKernelMonomial b a p) : Co1) ∈ P) :
    7372800 ≤ Nat.card (generatedTwelfthProjectionPreimage P) := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have hk : 1024 ≤ Nat.card (generatedTwelfthProjectionRootAction P).ker := by
    have h := Nat.card_le_card_of_injective (generatedTwelfthProjectionKernelEnumeration P hkernel)
      (generatedTwelfth_projection_kernel_enumeration_injective P hkernel)
    have hsize : Nat.card (Bool × Fin 32 × Fin 16) = 1024 := by
      norm_num [Nat.card_eq_fintype_card]
    rwa [hsize] at h
  apply generatedTwelfth_generic_group_lower (generatedTwelfthProjectionRootAction P)
    (generatedTwelfthProjectionRootWitness P hroot) _ hk
  intro n r
  exact generatedTwelfth_projection_root_word_actual P hroot
    (generatedTwelfthMatrixFixerRootWitnessWord n) r

/-- Every actual preimage projection is a genuine value in the intended subgroup. -/
def generatedTwelfthPreimageConwayProjection (P : Subgroup Co1) :
    generatedTwelfthProjectionPreimage P →* Co1 :=
  generatedTwelfthMatrixConwayProjection.comp (generatedTwelfthProjectionPreimage P).subtype

/-- The genuine preimage projection kernel injects into the two actual scalar lattice signs. -/
def generatedTwelfthPreimageSignsEmbedding (P : Subgroup Co1)
    (k : (generatedTwelfthPreimageConwayProjection P).ker) : signsSubgroup :=
  ⟨k.val.val.val.val, by
    apply (QuotientGroup.eq_one_iff _).mp
    exact k.property⟩

/-- Distinct actual projection-kernel elements remain distinct physical scalar signs. -/
theorem generatedTwelfth_preimage_signs_embedding_injective (P : Subgroup Co1) :
    Function.Injective (generatedTwelfthPreimageSignsEmbedding P) := by
  intro k l h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun s : signsSubgroup => s.val) h

/-- No more than two actual scalar lattice signs lie over any attained Conway value. -/
theorem generatedTwelfth_projection_preimage_upper (P : Subgroup Co1) :
    Nat.card (generatedTwelfthProjectionPreimage P) ≤ 2 * Nat.card P := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let : Finite Co1 := co1_finite
  let f := generatedTwelfthPreimageConwayProjection P
  have hker : Nat.card f.ker ≤ 2 := by
    have h := Nat.card_le_card_of_injective (generatedTwelfthPreimageSignsEmbedding P)
      (generatedTwelfth_preimage_signs_embedding_injective P)
    rwa [signsSubgroup_card] at h
  have hrange : f.range ≤ P := by
    rintro c ⟨g, rfl⟩
    exact g.property
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hcard
  have h := Nat.mul_le_mul hker (Subgroup.card_le_of_le hrange)
  rwa [hcard] at h

/-- All unchanged original root witnesses and physical kernel words force at least
3,686,400 genuinely attained Conway values. -/
theorem generatedTwelfth_projection_card_lower_generic (P : Subgroup Co1)
    (hroot : ∀ g : Fin 3, (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) ∈ P)
    (hkernel : ∀ (b : Bool) (a : Fin 32) (p : Fin 16),
      (QuotientGroup.mk (generatedTwelfthRootKernelMonomial b a p) : Co1) ∈ P) :
    3686400 ≤ Nat.card P := by
  have h0 := generatedTwelfth_projection_preimage_lower P hroot hkernel
  have h1 := generatedTwelfth_projection_preimage_upper P
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
