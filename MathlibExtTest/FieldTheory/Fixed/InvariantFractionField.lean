/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Fixed.InvariantFractionField

@[expose] public section

open CerednikDrinfeld.Mumford Polynomial

open scoped CerednikDrinfeld.Mumford

noncomputable section

namespace InvariantFractionFieldTest

/-- The automorphism group of `ℚ[X]` over `ℚ`, acting on `ℚ[X]`, is a
nontrivial instance of the invariant-field setup: membership in the
invariant field is the characterization by fixed points. -/
example (x : FractionRing ℚ[X]) :
    x ∈ invariantField ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ↔
      ∀ g : ℚ[X] ≃ₐ[ℚ] ℚ[X], g • x = x :=
  mem_invariantField_iff ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] x

/-- For a subgroup, membership is fixedness by that subgroup alone, and the
full invariant field is the top-subgroup case. -/
example (Γ : Subgroup (ℚ[X] ≃ₐ[ℚ] ℚ[X])) (x : FractionRing ℚ[X]) :
    x ∈ invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] Γ ↔
      ∀ γ : ℚ[X] ≃ₐ[ℚ] ℚ[X], γ ∈ Γ → γ • x = x :=
  mem_invariantFieldOf_iff ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] Γ x

example :
    invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊤ =
      invariantField ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] :=
  invariantFieldOf_top ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X]

/-- The invariant field is contained in every subgroup fixed field. -/
example (Γ : Subgroup (ℚ[X] ≃ₐ[ℚ] ℚ[X])) :
    invariantField ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ≤
      invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] Γ :=
  invariantField_le_invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] Γ

example :
    (1 : AmbientSemilinearAut ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X]).fracMap =
      RingEquiv.refl (FractionRing ℚ[X]) :=
  AmbientSemilinearAut.fracMap_one

/-- The substitution `X ↦ X + 1`, an automorphism of `ℚ[X]` that is not
its own inverse. -/
abbrev shiftX : ℚ[X] ≃ₐ[ℚ] ℚ[X] := algEquivAevalXAddC 1

theorem shiftX_smul_X : shiftX • (X : ℚ[X]) = X + 1 := by
  rw [AlgEquiv.smul_def, algEquivAevalXAddC_apply, aeval_X, C_1]

/-- Every element of the fraction field is fixed by the trivial subgroup. -/
theorem mem_invariantFieldOf_bot (x : FractionRing ℚ[X]) :
    x ∈ invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊥ := fun γ hγ => by
  rw [Subgroup.mem_bot] at hγ
  rw [hγ, one_smul]

/-- The element `X` of the field fixed by the trivial subgroup. -/
abbrev xBot : invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊥ :=
  ⟨algebraMap ℚ[X] (FractionRing ℚ[X]) X, mem_invariantFieldOf_bot _⟩

/-- The residual action on the field fixed by the trivial normal subgroup is
the action itself: the shift sends `X` to `X + 1`, not to `X - 1`. -/
theorem coe_residualAct_bot_shiftX :
    ((residualAct ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊥ shiftX xBot :
        invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊥) : FractionRing ℚ[X]) =
      algebraMap ℚ[X] (FractionRing ℚ[X]) (X + 1) := by
  rw [coe_residualAct, frac_smul_algebraMap, shiftX_smul_X]

/-- So the residual action of the trivial normal subgroup is not trivial. -/
example : residualAct ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊥ shiftX ≠ 1 := fun h => by
  have hx := coe_residualAct_bot_shiftX
  rw [h] at hx
  change algebraMap ℚ[X] (FractionRing ℚ[X]) X =
    algebraMap ℚ[X] (FractionRing ℚ[X]) (X + 1) at hx
  have hX := IsFractionRing.injective ℚ[X] (FractionRing ℚ[X]) hx
  simp at hX

/-- The residual action of the top normal subgroup is trivial: every element
of the group lies in it. -/
example (g : ℚ[X] ≃ₐ[ℚ] ℚ[X]) : residualAct ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊤ g = 1 :=
  residualAct_eq_one_of_mem ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊤ (Subgroup.mem_top g)

/-- The shift lies in the normalizer of the trivial subgroup. -/
theorem shiftX_mem_normalizer_bot :
    shiftX ∈ Subgroup.normalizer ((⊥ : Subgroup (ℚ[X] ≃ₐ[ℚ] ℚ[X])) : Set (ℚ[X] ≃ₐ[ℚ] ℚ[X])) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top _

/-- The normalizer of the trivial subgroup acts on its fixed field through
the group action, and agrees with the residual action there. -/
example :
    ((normalizerAct ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊥ ⟨shiftX, shiftX_mem_normalizer_bot⟩ xBot :
        invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊥) : FractionRing ℚ[X]) =
      algebraMap ℚ[X] (FractionRing ℚ[X]) (X + 1) := by
  rw [normalizerAct_eq_residualAct]
  exact coe_residualAct_bot_shiftX

/-- Elements of the subgroup act trivially through the normalizer action. -/
example (n : Subgroup.normalizer
      ((⊤ : Subgroup (ℚ[X] ≃ₐ[ℚ] ℚ[X])) : Set (ℚ[X] ≃ₐ[ℚ] ℚ[X]))) :
    normalizerAct ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊤ n = 1 :=
  normalizerAct_eq_one_of_mem ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊤ (Subgroup.mem_top _)

/-- Conjugation transport from a subgroup to its conjugate by the shift
applies the shift. -/
example :
    ((conjTransport ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] shiftX ⊥
        ((⊥ : Subgroup (ℚ[X] ≃ₐ[ℚ] ℚ[X])).map (MulAut.conj shiftX).toMonoidHom)
        (mem_map_conj_iff (ℚ[X] ≃ₐ[ℚ] ℚ[X]) shiftX ⊥) xBot :
        invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X]
          ((⊥ : Subgroup (ℚ[X] ≃ₐ[ℚ] ℚ[X])).map (MulAut.conj shiftX).toMonoidHom)) :
        FractionRing ℚ[X]) =
      algebraMap ℚ[X] (FractionRing ℚ[X]) (X + 1) := by
  rw [coe_conjTransport, frac_smul_algebraMap, shiftX_smul_X]

/-- On the complete graph on `Fin 2`, the transposition exchanges the two
vertex types: it adds one to the type of each vertex. -/
theorem isTypeExchanger_swap :
    IsTypeExchanger (⊤ : SimpleGraph (Fin 2)) 0 (Equiv.swap (0 : Fin 2) 1) := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [Equiv.Perm.smul_def, Equiv.swap_apply_left, vertexType_apply, vertexType_apply,
      SimpleGraph.dist_top_of_ne (show (0 : Fin 2) ≠ 1 by decide), SimpleGraph.dist_self]
    decide
  · rw [Equiv.Perm.smul_def, Equiv.swap_apply_right, vertexType_apply, vertexType_apply,
      SimpleGraph.dist_self, SimpleGraph.dist_top_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
    decide

example : HasTypeExchanger (Equiv.Perm (Fin 2)) (⊤ : SimpleGraph (Fin 2)) 0 :=
  ⟨_, isTypeExchanger_swap⟩

/-- A type exchanger is not type-preserving. -/
example :
    Equiv.swap (0 : Fin 2) 1 ∉ typePreserving (Equiv.Perm (Fin 2)) (⊤ : SimpleGraph (Fin 2)) 0 :=
  isTypeExchanger_swap.notMem_typePreserving

/-- On the triangle, the transposition of `0` and `1` changes the type of `0`
but fixes the vertex `2` and its type: it is not type-preserving, and it is
not a type exchanger either. -/
example :
    Equiv.swap (0 : Fin 3) 1 ∉ typePreserving (Equiv.Perm (Fin 3)) (⊤ : SimpleGraph (Fin 3)) 0 ∧
      ¬IsTypeExchanger (⊤ : SimpleGraph (Fin 3)) 0 (Equiv.swap (0 : Fin 3) 1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h0 := (mem_typePreserving_iff _ _ _).1 h 0
    rw [Equiv.Perm.smul_def, Equiv.swap_apply_left, vertexType_apply, vertexType_apply,
      SimpleGraph.dist_top_of_ne (show (0 : Fin 3) ≠ 1 by decide),
      SimpleGraph.dist_self] at h0
    exact absurd h0 (by decide)
  · have h2 := h 2
    rw [Equiv.Perm.smul_def,
      Equiv.swap_apply_of_ne_of_ne (show (2 : Fin 3) ≠ 0 by decide)
        (show (2 : Fin 3) ≠ 1 by decide), left_eq_add] at h2
    exact absurd h2 (by decide)

end InvariantFractionFieldTest

end
