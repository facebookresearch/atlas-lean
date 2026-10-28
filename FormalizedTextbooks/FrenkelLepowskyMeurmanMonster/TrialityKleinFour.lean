/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The actual local central involution and its triality conjugates.
The central spin sign fixes the matrix and short blocks and negates spin tensors;
Seysen's dictionary transport therefore gives the signs (+,-,-) on X,Y,Z.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalStructure
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

@[expose] public section
open scoped TensorProduct
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine local central involution acting in the fixed Griess dictionary. -/
noncomputable def localCentralGriess : GriessSpace ≃ₗ[ℝ] GriessSpace :=
  rhoLocal (inclQ qCentralInvolution)

private theorem central_fiber_spin (x : SpinSpace) :
    (localFiberIncl qCentralInvolution).val.1.val x = -x := by
  change spinRepresentation (qCentral 1) x = -x
  rw [spinRepresentation_central]
  simp [qSign]

private theorem central_fiber_short (x : GriessShortIndex → ℝ) :
    localShortRepresentation (localFiberIncl qCentralInvolution) x = x := by
  let f := localFiberIncl qCentralInvolution
  have hspin : ∀ u, f.val.1.val u = qSign (1 : ZMod 2) • u := by
    intro u
    change spinRepresentation (qCentral 1) u = qSign (1 : ZMod 2) • u
    exact spinRepresentation_central 1 u
  have ha := spinConjugation_scalar f.val.1 1 hspin
  have hphase (r : GriessShortIndex) : localShortPhase f r = 0 := by
    change Multiplicative.toAdd (spinConjugation f.val.1 (griessShortQ r)).coeff = 0
    rw [ha]
    exact griessShortQ_coeff r
  have hp (r : GriessShortIndex) : griessShortPermutation f.val.2 r = r := by
    change griessShortPermutation 1 r = r
    rw [map_one]
    rfl
  funext r
  have h := localShortOperator_image f x r
  rw [hp, hphase, qSign_zero, one_mul] at h
  exact h

private theorem central_fiber_tensor_action
    (x : SpinSpace ⊗[ℝ] (Fin 24 → ℝ)) :
    localTensorAction (localFiberIncl qCentralInvolution) x = -x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change TensorProduct.congr _ _ (a ⊗ₜ[ℝ] b) = -(a ⊗ₜ[ℝ] b)
    rw [TensorProduct.congr_tmul, central_fiber_spin]
    change (-a) ⊗ₜ[ℝ] b = -(a ⊗ₜ[ℝ] b)
    exact TensorProduct.neg_tmul a b
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]

private theorem central_fiber_tensor (x : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation (localFiberIncl qCentralInvolution) x = -x := by
  obtain ⟨u, rfl⟩ := conwayTensorCoordinates.surjective x
  rw [localTensorRepresentation_coordinates, central_fiber_tensor_action, map_neg]

/-- The genuine central involution fixes the matrix and short blocks and negates tensors. -/
theorem localCentralGriess_encode (x : GriessSpace) :
    griessConwayEncode (localCentralGriess x) =
      ((griessConwayEncode x).1, ((griessConwayEncode x).2.1, -(griessConwayEncode x).2.2)) := by
  change griessConwayEncode (localGriessRepresentation (localFiberIncl qCentralInvolution) x) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply,
    central_fiber_short, central_fiber_tensor]
  change (conwayMatrixAction 1 (griessConwayEncode x).1,
    ((griessConwayEncode x).2.1, -(griessConwayEncode x).2.2)) = _
  rw [map_one]
  rfl

/-- The three dictionary signs fixing one of X,Y,Z and negating the other two. -/
noncomputable def trialityCentralBlockAction (k : Fin 3) : TrialityBlocks ≃ₗ[ℝ] TrialityBlocks :=
  (LinearEquiv.refl ℝ _).prodCongr ((LinearEquiv.refl ℝ _).prodCongr
    ((LinearEquiv.refl ℝ _).prodCongr
      (LinearEquiv.piCongrRight fun s : Fin 3 =>
        LinearEquiv.smulOfNeZero ℝ (Fin 49152 → ℝ)
          (if s = k then (1 : ℝ) else -1) (by split <;> norm_num))))

/-- The dictionary sign action fixes every other block and has the stated X,Y,Z row signs. -/
theorem trialityCentralBlockAction_apply (k : Fin 3) (b : TrialityBlocks) :
    trialityCentralBlockAction k b =
      (b.1, (b.2.1, (b.2.2.1, fun s i => (if s = k then (1 : ℝ) else -1) * b.2.2.2 s i))) := by
  rfl

/-- Transport of the three diagonal dictionary sign operations to the actual Griess space. -/
noncomputable def trialityCentralSign (k : Fin 3) : GriessSpace ≃ₗ[ℝ] GriessSpace :=
  trialityBlocksEquiv.trans ((trialityCentralBlockAction k).trans trialityBlocksEquiv.symm)

/-- The signs in the fixed dictionary coordinates. -/
theorem trialityCentralSign_blocks (k : Fin 3) (x : GriessSpace) :
    trialityBlocksEquiv (trialityCentralSign k x) =
      trialityCentralBlockAction k (trialityBlocksEquiv x) := by
  simp only [trialityCentralSign, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

private theorem central_decode_blocks (z : ConwayRawSpace) :
    trialityBlocksEquiv (griessConwayDecode (z.1, (z.2.1, -z.2.2))) =
      trialityCentralBlockAction 0 (trialityBlocksEquiv (griessConwayDecode z)) := by
  simp only [griessConwayDecode, LinearEquiv.apply_symm_apply, trialityCentralBlockAction_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext s i
        simp only [Pi.neg_apply]
        by_cases hs : s = 0
        · simp only [hs, ite_true, one_mul]
        · simp only [hs, ite_false, neg_one_mul]
          split_ifs <;> ring

/-- The actual local central image is the X-positive dictionary sign operation;
this identifies the genuine action before taking any triality conjugates. -/
theorem localCentralGriess_eq_trialityCentralSign : localCentralGriess = trialityCentralSign 0 := by
  apply LinearEquiv.ext
  intro x
  apply trialityBlocksEquiv.injective
  have h := congrArg griessConwayDecode (localCentralGriess_encode x)
  rw [griessConwayDecode_encode] at h
  rw [h, central_decode_blocks, griessConwayDecode_encode, trialityCentralSign_blocks]

/-- Every dictionary central sign is an involution. -/
theorem trialityCentralBlockAction_square (k : Fin 3) :
    trialityCentralBlockAction k * trialityCentralBlockAction k = 1 := by
  apply LinearEquiv.ext
  intro b
  simp only [LinearEquiv.mul_apply, trialityCentralBlockAction_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext s i
        by_cases hs : s = k <;> simp [hs]

/-- The three diagonal block sign actions commute. -/
theorem trialityCentralBlockAction_commute (k l : Fin 3) :
    trialityCentralBlockAction k * trialityCentralBlockAction l =
      trialityCentralBlockAction l * trialityCentralBlockAction k := by
  apply LinearEquiv.ext
  intro b
  simp only [LinearEquiv.mul_apply, trialityCentralBlockAction_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext s i
        ring

/-- The first two nonidentity sign actions multiply to the third. -/
theorem trialityCentralBlockAction_zero_mul_one :
    trialityCentralBlockAction 0 * trialityCentralBlockAction 1 = trialityCentralBlockAction 2 := by
  apply LinearEquiv.ext
  intro b
  simp only [LinearEquiv.mul_apply, trialityCentralBlockAction_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext s i
        fin_cases s <;> norm_num

/-- Different positive rows give distinct nonidentity sign operations. -/
theorem trialityCentralBlockAction_injective : Function.Injective trialityCentralBlockAction := by
  intro k l h
  by_contra hkl
  let b : TrialityBlocks := (0, (0, (0, fun s _ => if s = k then 1 else 0)))
  have he := congrArg (fun E : TrialityBlocks ≃ₗ[ℝ] TrialityBlocks => (E b).2.2.2 k 0) h
  simp only [trialityCentralBlockAction_apply, b, ite_true, ite_eq_right hkl] at he
  norm_num at he

/-- Each positive-row operation is nonidentity. -/
theorem trialityCentralBlockAction_ne_one (k : Fin 3) : trialityCentralBlockAction k ≠ 1 := by
  let l : Fin 3 := if k = 0 then 1 else 0
  have hl : l ≠ k := by
    dsimp only [l]
    split_ifs with hk
    · subst k
      decide
    · exact Ne.symm hk
  let b : TrialityBlocks := (0, (0, (0, fun s _ => if s = l then 1 else 0)))
  intro h
  have he := congrArg (fun E : TrialityBlocks ≃ₗ[ℝ] TrialityBlocks => (E b).2.2.2 l 0) h
  simp only [trialityCentralBlockAction_apply, b, ite_true, ite_eq_right hl] at he
  norm_num at he

private theorem trialityBlockAction_central_intertwine (k : Fin 3) :
    trialityBlockAction * trialityCentralBlockAction k =
      trialityCentralBlockAction (trialityCycle k) * trialityBlockAction := by
  apply LinearEquiv.ext
  intro b
  simp only [LinearEquiv.mul_apply, trialityCentralBlockAction_apply, trialityBlockAction,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext s i
        simp only [trialityCycleAction, LinearEquiv.piCongrLeft'_apply]
        simp only [Equiv.symm_apply_eq]

/-- Triality rotates the positive dictionary row of a central sign action. -/
theorem trialityCentralSign_conjugate (k : Fin 3) :
    sExtra * trialityCentralSign k * sExtra⁻¹ = trialityCentralSign (trialityCycle k) := by
  have hinter : sExtra * trialityCentralSign k =
      trialityCentralSign (trialityCycle k) * sExtra := by
    apply LinearEquiv.ext
    intro x
    apply trialityBlocksEquiv.injective
    simp only [LinearEquiv.mul_apply, sExtra, griessTriality, trialityCentralSign,
      LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact LinearEquiv.congr_fun (trialityBlockAction_central_intertwine k) (trialityBlocksEquiv x)
  rw [hinter, mul_assoc, mul_inv_cancel, mul_one]

/-- Every transported central sign is an involution. -/
theorem trialityCentralSign_square (k : Fin 3) :
    trialityCentralSign k * trialityCentralSign k = 1 := by
  change coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction k) *
    coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction k) = 1
  rw [← map_mul, trialityCentralBlockAction_square, map_one]

/-- The transported signs commute in the actual Griess linear group. -/
theorem trialityCentralSign_commute (k l : Fin 3) :
    trialityCentralSign k * trialityCentralSign l =
      trialityCentralSign l * trialityCentralSign k := by
  change coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction k) *
    coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction l) =
    coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction l) *
    coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction k)
  rw [← map_mul, ← map_mul, trialityCentralBlockAction_commute]

/-- The transported first two signs multiply to the third. -/
theorem trialityCentralSign_zero_mul_one :
    trialityCentralSign 0 * trialityCentralSign 1 = trialityCentralSign 2 := by
  change coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction 0) *
    coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction 1) =
    coordinateGLTransport trialityBlocksEquiv.symm (trialityCentralBlockAction 2)
  rw [← map_mul, trialityCentralBlockAction_zero_mul_one]

/-- The three transported signs remain pairwise distinct. -/
theorem trialityCentralSign_injective : Function.Injective trialityCentralSign := by
  intro k l h
  apply trialityCentralBlockAction_injective
  apply LinearEquiv.ext
  intro b
  have he := congrArg
    (fun E : GriessSpace ≃ₗ[ℝ] GriessSpace =>
      trialityBlocksEquiv (E (trialityBlocksEquiv.symm b))) h
  simpa only [trialityCentralSign_blocks, LinearEquiv.apply_symm_apply] using he

/-- No transported sign becomes identity. -/
theorem trialityCentralSign_ne_one (k : Fin 3) : trialityCentralSign k ≠ 1 := by
  intro h
  apply trialityCentralBlockAction_ne_one k
  apply LinearEquiv.ext
  intro b
  have he := congrArg
    (fun E : GriessSpace ≃ₗ[ℝ] GriessSpace =>
      trialityBlocksEquiv (E (trialityBlocksEquiv.symm b))) h
  simpa only [trialityCentralSign_blocks, LinearEquiv.coe_one, id_eq,
    LinearEquiv.apply_symm_apply] using he

private theorem trialityCycle_zero : trialityCycle 0 = 1 := by decide +kernel
private theorem trialityCycle_one : trialityCycle 1 = 2 := by decide +kernel

/-- The first genuine triality conjugate has the Y-positive sign pattern. -/
theorem localCentralGriess_conjugate :
    sExtra * localCentralGriess * sExtra⁻¹ = trialityCentralSign 1 := by
  rw [localCentralGriess_eq_trialityCentralSign, trialityCentralSign_conjugate, trialityCycle_zero]

/-- The second genuine triality conjugate has the Z-positive sign pattern. -/
theorem localCentralGriess_conjugate_square :
    sExtra ^ 2 * localCentralGriess * (sExtra ^ 2)⁻¹ = trialityCentralSign 2 := by
  calc
    _ = sExtra * (sExtra * localCentralGriess * sExtra⁻¹) * sExtra⁻¹ := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    _ = trialityCentralSign 2 := by
      rw [localCentralGriess_conjugate, trialityCentralSign_conjugate, trialityCycle_one]

/-- The genuine local central involution belongs to the generated Monster candidate. -/
theorem localCentralGriess_mem_G : localCentralGriess ∈ G := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨inclQ qCentralInvolution, rfl⟩

/-- The actual triality generator belongs to the generated group. -/
theorem sExtra_mem_generated_G : sExtra ∈ G := by
  apply Subgroup.subset_closure
  exact Or.inr rfl

/-- All three actual central sign operations belong to the generated group. -/
theorem trialityCentralSign_mem_G (k : Fin 3) : trialityCentralSign k ∈ G := by
  have hz : trialityCentralSign 0 ∈ G := by
    rw [← localCentralGriess_eq_trialityCentralSign]
    exact localCentralGriess_mem_G
  have h1 : trialityCentralSign 1 ∈ G := by
    rw [← localCentralGriess_conjugate]
    exact G.mul_mem (G.mul_mem sExtra_mem_generated_G localCentralGriess_mem_G)
      (G.inv_mem sExtra_mem_generated_G)
  have h2 : trialityCentralSign 2 ∈ G := by
    rw [← trialityCentralSign_zero_mul_one]
    exact G.mul_mem hz h1
  fin_cases k
  · exact hz
  · exact h1
  · exact h2

private theorem trialityCentralSign_zero_mul_two :
    trialityCentralSign 0 * trialityCentralSign 2 = trialityCentralSign 1 := by
  rw [← trialityCentralSign_zero_mul_one, ← mul_assoc, trialityCentralSign_square, one_mul]

private theorem trialityCentralSign_one_mul_two :
    trialityCentralSign 1 * trialityCentralSign 2 = trialityCentralSign 0 := by
  rw [← trialityCentralSign_zero_mul_one,
    ← trialityCentralSign_commute 1 0, ← mul_assoc, trialityCentralSign_square, one_mul]

private theorem trialityCentralSign_product_mem (k l : Fin 3) :
    trialityCentralSign k * trialityCentralSign l = 1 ∨
      ∃ m, trialityCentralSign k * trialityCentralSign l = trialityCentralSign m := by
  by_cases hkl : k = l
  · subst l
    exact Or.inl (trialityCentralSign_square k)
  · right
    fin_cases k <;> fin_cases l
    · exact (hkl rfl).elim
    · exact ⟨2, trialityCentralSign_zero_mul_one⟩
    · exact ⟨1, trialityCentralSign_zero_mul_two⟩
    · exact ⟨2, (trialityCentralSign_commute 1 0).trans trialityCentralSign_zero_mul_one⟩
    · exact (hkl rfl).elim
    · exact ⟨0, trialityCentralSign_one_mul_two⟩
    · exact ⟨1, (trialityCentralSign_commute 2 0).trans trialityCentralSign_zero_mul_two⟩
    · exact ⟨0, (trialityCentralSign_commute 2 1).trans trialityCentralSign_one_mul_two⟩
    · exact (hkl rfl).elim

/-- The concrete Klein four subgroup consisting of identity and the three actual central signs. -/
noncomputable def trialityKleinFour : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) where
  carrier := {g | g = 1 ∨ ∃ k, g = trialityCentralSign k}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | ⟨k, rfl⟩) (rfl | ⟨l, rfl⟩)
    · exact Or.inl (one_mul 1)
    · exact Or.inr ⟨l, one_mul _⟩
    · exact Or.inr ⟨k, mul_one _⟩
    · exact trialityCentralSign_product_mem k l
  inv_mem' := by
    rintro a (rfl | ⟨k, rfl⟩)
    · exact Or.inl inv_one
    · exact Or.inr ⟨k, inv_eq_of_mul_eq_one_left (trialityCentralSign_square k)⟩

/-- The concrete Klein four subgroup lies in the generated group. -/
theorem trialityKleinFour_le_G : trialityKleinFour ≤ G := by
  rintro g (rfl | ⟨k, rfl⟩)
  · exact G.one_mem
  · exact trialityCentralSign_mem_G k

/-- Enumerate the Klein four subgroup by identity and its three positive-row labels. -/
noncomputable def trialityKleinFourEquiv : (Unit ⊕ Fin 3) ≃ trialityKleinFour :=
  Equiv.ofBijective
    (fun u => match u with
      | Sum.inl _ => ⟨1, Or.inl rfl⟩
      | Sum.inr k => ⟨trialityCentralSign k, Or.inr ⟨k, rfl⟩⟩) (by
      constructor
      · intro a b h
        cases a with
        | inl a =>
          cases b with
          | inl b => rfl
          | inr b =>
            exact (trialityCentralSign_ne_one b (congrArg Subtype.val h).symm).elim
        | inr a =>
          cases b with
          | inl b => exact (trialityCentralSign_ne_one a (congrArg Subtype.val h)).elim
          | inr b =>
            exact congrArg Sum.inr (trialityCentralSign_injective (congrArg Subtype.val h))
      · rintro ⟨g, hg⟩
        rcases hg with rfl | ⟨k, rfl⟩
        · exact ⟨Sum.inl (), rfl⟩
        · exact ⟨Sum.inr k, rfl⟩)

/-- The actual subgroup generated by the three central sign patterns has order four. -/
theorem trialityKleinFour_card : Nat.card trialityKleinFour = 4 := by
  rw [← Nat.card_congr trialityKleinFourEquiv]
  simp

/-- The local central involution times its first triality conjugate is its second conjugate. -/
theorem localCentralGriess_mul_conjugate :
    localCentralGriess * (sExtra * localCentralGriess * sExtra⁻¹) =
      sExtra ^ 2 * localCentralGriess * (sExtra ^ 2)⁻¹ := by
  rw [localCentralGriess_eq_trialityCentralSign, trialityCentralSign_conjugate,
    trialityCycle_zero, trialityCentralSign_zero_mul_one]
  rw [← localCentralGriess_eq_trialityCentralSign, localCentralGriess_conjugate_square]

/-- The genuine local central involution commutes with its first triality conjugate. -/
theorem localCentralGriess_commute_conjugate :
    localCentralGriess * (sExtra * localCentralGriess * sExtra⁻¹) =
      (sExtra * localCentralGriess * sExtra⁻¹) * localCentralGriess := by
  rw [localCentralGriess_eq_trialityCentralSign, trialityCentralSign_conjugate,
    trialityCycle_zero, trialityCentralSign_commute]

/-- The concrete subgroup is generated by the genuine local central involution
and its first triality conjugate. -/
theorem trialityKleinFour_eq_closure :
    trialityKleinFour = Subgroup.closure
      {localCentralGriess, sExtra * localCentralGriess * sExtra⁻¹} := by
  let K := Subgroup.closure {localCentralGriess, sExtra * localCentralGriess * sExtra⁻¹}
  have h0 : trialityCentralSign 0 ∈ K := by
    rw [← localCentralGriess_eq_trialityCentralSign]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have h1 : trialityCentralSign 1 ∈ K := by
    rw [← localCentralGriess_conjugate]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have h2 : trialityCentralSign 2 ∈ K := by
    rw [← trialityCentralSign_zero_mul_one]
    exact K.mul_mem h0 h1
  apply le_antisymm
  · rintro g (rfl | ⟨k, rfl⟩)
    · exact K.one_mem
    · fin_cases k
      · exact h0
      · exact h1
      · exact h2
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact Or.inr ⟨0, localCentralGriess_eq_trialityCentralSign⟩
    · have he : g = sExtra * localCentralGriess * sExtra⁻¹ := Set.mem_singleton_iff.mp hg
      subst g
      exact Or.inr ⟨1, localCentralGriess_conjugate⟩

/-- Every element of the actual four-element subgroup has square one. -/
theorem trialityKleinFour_square (g : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (hg : g ∈ trialityKleinFour) : g * g = 1 := by
  rcases hg with rfl | ⟨k, rfl⟩
  · exact one_mul 1
  · exact trialityCentralSign_square k

/-- The actual four-element subgroup is abelian. -/
theorem trialityKleinFour_commute (g h : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (hg : g ∈ trialityKleinFour) (hh : h ∈ trialityKleinFour) : g * h = h * g := by
  rcases hg with rfl | ⟨k, rfl⟩
  · simp only [one_mul, mul_one]
  · rcases hh with rfl | ⟨l, rfl⟩
    · simp only [one_mul, mul_one]
    · exact trialityCentralSign_commute k l

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
