/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Fixed.InvariantFractionField
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section

open CerednikDrinfeld.Mumford Polynomial

open scoped CerednikDrinfeld.Mumford

noncomputable section

namespace InvariantFractionFieldTest

variable (k : Type*) [Field k]

/-- The automorphism group of `k[X]` over a field `k`, acting on `k[X]`, is a
nontrivial instance of the setup: the Mumford field is Mathlib's field of fixed
points of the induced action on the fraction field. -/
example (x : FractionRing k[X]) :
    x ∈ mumfordField k (k[X] ≃ₐ[k] k[X]) k[X] ↔ ∀ g : k[X] ≃ₐ[k] k[X], g • x = x :=
  FixedPoints.mem_intermediateField_iff

/-- For a subgroup, its fixed field is Mathlib's fixed field of the restricted
action: membership is fixedness by the elements of the subgroup. -/
example (Γ : Subgroup (k[X] ≃ₐ[k] k[X])) (x : FractionRing k[X]) :
    x ∈ (FixedPoints.intermediateField Γ : IntermediateField k (FractionRing k[X])) ↔
      ∀ γ : Γ, γ • x = x :=
  FixedPoints.mem_intermediateField_iff

/-- The identity ambient automorphism extends to the identity of the fraction field,
by Mathlib's `IsFractionRing.ringEquivOfRingEquiv_refl`. -/
example :
    (1 : AmbientSemilinearAut k (k[X] ≃ₐ[k] k[X]) k[X]).fracMap =
      RingEquiv.refl (FractionRing k[X]) :=
  IsFractionRing.ringEquivOfRingEquiv_refl

/-- The substitution `X ↦ X + 1`, an automorphism of `k[X]` other than the
identity. -/
abbrev shiftX : k[X] ≃ₐ[k] k[X] := algEquivAevalXAddC 1

theorem shiftX_smul_X : shiftX k • (X : k[X]) = X + 1 := by
  rw [AlgEquiv.smul_def, algEquivAevalXAddC_apply, aeval_X, C_1]

/-- Every element of the fraction field is fixed by the trivial subgroup. -/
theorem mem_fixedPoints_bot (x : FractionRing k[X]) :
    x ∈ (FixedPoints.intermediateField (⊥ : Subgroup (k[X] ≃ₐ[k] k[X])) :
      IntermediateField k (FractionRing k[X])) := fun γ => by
  change (γ : k[X] ≃ₐ[k] k[X]) • x = x
  rw [Subgroup.mem_bot.mp γ.2, one_smul]

/-- The element `X` of the field fixed by the trivial subgroup. -/
abbrev xBot : (FixedPoints.intermediateField (⊥ : Subgroup (k[X] ≃ₐ[k] k[X])) :
    IntermediateField k (FractionRing k[X])) :=
  ⟨algebraMap k[X] (FractionRing k[X]) X, mem_fixedPoints_bot k _⟩

/-- The residual action on the field fixed by the trivial normal subgroup is
the action itself: the shift sends `X` to `X + 1`. -/
theorem coe_residualAct_bot_shiftX :
    ((residualAct k (k[X] ≃ₐ[k] k[X]) k[X] ⊥ (shiftX k) (xBot k) :
        (FixedPoints.intermediateField (⊥ : Subgroup (k[X] ≃ₐ[k] k[X])) :
          IntermediateField k (FractionRing k[X]))) : FractionRing k[X]) =
      algebraMap k[X] (FractionRing k[X]) (X + 1) := by
  rw [coe_residualAct, ← algebraMap.smul', shiftX_smul_X]

/-- So the residual action of the trivial normal subgroup is not trivial. -/
example : residualAct k (k[X] ≃ₐ[k] k[X]) k[X] ⊥ (shiftX k) ≠ 1 := fun h => by
  have hx := coe_residualAct_bot_shiftX k
  rw [h] at hx
  change algebraMap k[X] (FractionRing k[X]) X =
    algebraMap k[X] (FractionRing k[X]) (X + 1) at hx
  have hX := IsFractionRing.injective k[X] (FractionRing k[X]) hx
  simp at hX

/-- The residual action of the top normal subgroup is trivial: every element
of the group lies in it. -/
example (g : k[X] ≃ₐ[k] k[X]) : residualAct k (k[X] ≃ₐ[k] k[X]) k[X] ⊤ g = 1 :=
  residualAct_eq_one_of_mem k (k[X] ≃ₐ[k] k[X]) k[X] ⊤ (Subgroup.mem_top g)

/-- The shift lies in the normalizer of the trivial subgroup. -/
theorem shiftX_mem_normalizer_bot :
    shiftX k ∈
      Subgroup.normalizer ((⊥ : Subgroup (k[X] ≃ₐ[k] k[X])) : Set (k[X] ≃ₐ[k] k[X])) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top _

/-- The normalizer of the trivial subgroup acts on its fixed field through
the group action, and agrees with the residual action there. -/
example :
    ((normalizerAct k (k[X] ≃ₐ[k] k[X]) k[X] ⊥ ⟨shiftX k, shiftX_mem_normalizer_bot k⟩
        (xBot k) :
        (FixedPoints.intermediateField (⊥ : Subgroup (k[X] ≃ₐ[k] k[X])) :
          IntermediateField k (FractionRing k[X]))) : FractionRing k[X]) =
      algebraMap k[X] (FractionRing k[X]) (X + 1) := by
  rw [normalizerAct_eq_residualAct]
  exact coe_residualAct_bot_shiftX k

/-- Elements of the subgroup act trivially through the normalizer action. -/
example (n : Subgroup.normalizer
      ((⊤ : Subgroup (k[X] ≃ₐ[k] k[X])) : Set (k[X] ≃ₐ[k] k[X]))) :
    normalizerAct k (k[X] ≃ₐ[k] k[X]) k[X] ⊤ n = 1 :=
  normalizerAct_eq_one_of_mem k (k[X] ≃ₐ[k] k[X]) k[X] ⊤ (Subgroup.mem_top _)

/-- Conjugation transport from a subgroup to its conjugate by the shift
applies the shift. -/
example :
    ((conjTransport k (k[X] ≃ₐ[k] k[X]) k[X] (shiftX k) ⊥
        ((⊥ : Subgroup (k[X] ≃ₐ[k] k[X])).map (MulAut.conj (shiftX k)).toMonoidHom)
        (mem_map_conj_iff (k[X] ≃ₐ[k] k[X]) (shiftX k) ⊥) (xBot k) :
        (FixedPoints.intermediateField
            ((⊥ : Subgroup (k[X] ≃ₐ[k] k[X])).map (MulAut.conj (shiftX k)).toMonoidHom) :
          IntermediateField k (FractionRing k[X]))) : FractionRing k[X]) =
      algebraMap k[X] (FractionRing k[X]) (X + 1) := by
  rw [coe_conjTransport, ← algebraMap.smul', shiftX_smul_X]

/-- The `k`-automorphism of `k[X₀, X₁, X₂]` permuting the variables cyclically,
`X₀ ↦ X₁ ↦ X₂ ↦ X₀`. It is not an involution, so the actions of it and of its inverse
differ. -/
abbrev rot : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k :=
  MvPolynomial.renameEquiv k (finRotate 3)

/-- The `k`-automorphism of `k[X₀, X₁, X₂]` exchanging `X₀` and `X₂`; it fixes `X₁`. -/
abbrev swap02 : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k :=
  MvPolynomial.renameEquiv k (Equiv.swap 0 2)

theorem rot_smul_X0 : rot k • (MvPolynomial.X 0 : MvPolynomial (Fin 3) k) = .X 1 := by
  rw [AlgEquiv.smul_def, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  exact congrArg MvPolynomial.X (by decide)

/-- The inverse of `rot` sends `X₀` to `X₂`, not to `X₁`. -/
example : (rot k)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 3) k) = .X 2 := by
  rw [AlgEquiv.smul_def, AlgEquiv.aut_inv, MvPolynomial.renameEquiv_symm,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  exact congrArg MvPolynomial.X (by decide)

/-- The stabilizer of `X₀` in the automorphism group of `k[X₀, X₁, X₂]`. -/
abbrev stab0 : Subgroup (MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k) :=
  MulAction.stabilizer _ (MvPolynomial.X 0 : MvPolynomial (Fin 3) k)

/-- The stabilizer of `X₁`, the conjugate of `stab0` by `rot`. -/
abbrev stab1 : Subgroup (MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k) :=
  MulAction.stabilizer _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) k)

/-- Conjugation by `rot` carries `stab0` onto `stab1`, the hypothesis of the transport. -/
theorem mem_stab1_iff (d : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k) :
    d ∈ stab1 k ↔ (rot k)⁻¹ * d * rot k ∈ stab0 k := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, mul_smul, mul_smul,
    rot_smul_X0, inv_smul_eq_iff, rot_smul_X0]

/-- The direction of the transport's hypothesis: conjugation by `rot`, Mathlib's
`MulAut.conj` (`d ↦ g * d * g⁻¹`), carries `stab0` onto `stab1`. -/
example : stab1 k = (stab0 k).map (MulAut.conj (rot k)).toMonoidHom := by
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, rot_smul_X0]

/-- `X₀` in the fraction field of `k[X₀, X₁, X₂]`. -/
abbrev x0 : FractionRing (MvPolynomial (Fin 3) k) :=
  algebraMap _ _ (MvPolynomial.X 0 : MvPolynomial (Fin 3) k)

/-- `X₁` in the fraction field of `k[X₀, X₁, X₂]`. -/
abbrev x1 : FractionRing (MvPolynomial (Fin 3) k) :=
  algebraMap _ _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) k)

theorem x0_mem : x0 k ∈ (FixedPoints.intermediateField (stab0 k) :
    IntermediateField k (FractionRing (MvPolynomial (Fin 3) k))) := fun γ => by
  change (γ : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k) • x0 k = x0 k
  rw [← algebraMap.smul', MulAction.mem_stabilizer_iff.mp γ.2]

theorem x1_mem : x1 k ∈ (FixedPoints.intermediateField (stab1 k) :
    IntermediateField k (FractionRing (MvPolynomial (Fin 3) k))) := fun γ => by
  change (γ : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k) • x1 k = x1 k
  rw [← algebraMap.smul', MulAction.mem_stabilizer_iff.mp γ.2]

/-- The two conjugate subgroups have distinct fixed fields: `swap02` fixes `X₁`, so it lies in
`stab1`, but it moves `X₀`, so `X₀` is fixed by `stab0` and not by `stab1`. -/
theorem x0_not_mem : x0 k ∉ (FixedPoints.intermediateField (stab1 k) :
    IntermediateField k (FractionRing (MvPolynomial (Fin 3) k))) := fun h => by
  have h02 : swap02 k ∈ stab1 k := by
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_X, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  have hfix := h ⟨swap02 k, h02⟩
  change swap02 k • x0 k = x0 k at hfix
  rw [← algebraMap.smul', AlgEquiv.smul_def, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, Equiv.swap_apply_left] at hfix
  exact absurd (MvPolynomial.X_injective (IsFractionRing.injective _ _ hfix)) (by decide)

/-- Transport between the distinct fixed fields of `stab0` and of its conjugate `stab1`
applies `rot`: it sends `X₀` to `X₁`. -/
theorem conjTransport_x0 :
    ((conjTransport k (MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k)
        (MvPolynomial (Fin 3) k) (rot k) (stab0 k) (stab1 k) (mem_stab1_iff k)
        ⟨x0 k, x0_mem k⟩ :
        (FixedPoints.intermediateField (stab1 k) :
          IntermediateField k (FractionRing (MvPolynomial (Fin 3) k)))) :
        FractionRing (MvPolynomial (Fin 3) k)) = x1 k := by
  change rot k • x0 k = x1 k
  rw [← algebraMap.smul', rot_smul_X0]

/-- In the other direction, the inverse transport applies the inverse of `rot`: it sends
`X₁` back to `X₀`. -/
theorem conjTransport_symm_x1 :
    (((conjTransport k (MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 3) k)
        (MvPolynomial (Fin 3) k) (rot k) (stab0 k) (stab1 k) (mem_stab1_iff k)).symm
        ⟨x1 k, x1_mem k⟩ :
        (FixedPoints.intermediateField (stab0 k) :
          IntermediateField k (FractionRing (MvPolynomial (Fin 3) k)))) :
        FractionRing (MvPolynomial (Fin 3) k)) = x0 k := by
  change (rot k)⁻¹ • x1 k = x0 k
  rw [← algebraMap.smul']
  exact congrArg _ (inv_smul_eq_iff.mpr (rot_smul_X0 k).symm)

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
