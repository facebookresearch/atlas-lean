/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IteratedCup
public import MathlibExt.RepresentationTheory.Rep.ResTensor

/-!
# Positive iterated cups under restriction

An iterated cup formed after restricting the acting group is normalized into
the restriction of the original tensor-power coefficient.  Its head--tail
decomposition is compatible with the corresponding restricted coefficient
decomposition in every positive weight.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- An iterated cup over a restricted group action, normalized into the
restriction of the original positive tensor-power coefficient. -/
noncomputable def restrictedIteratedCupClassSucc
    (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology (Rep.res f A) 1) :
    groupCohomology
      (Rep.res f (TensorPower.tensorPowObj A (n + 1))) (n + 1) :=
  (map (MonoidHom.id H)
    (Rep.resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n).inv
    (n + 1)).hom
      (iteratedCupClassSucc (Rep.res f A) n x)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The normalized restricted iterated cup decomposes into its first class
and normalized restricted iterated tail. -/
theorem restrictedIteratedCupClassSucc_headTail
    (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin (n + 2) → groupCohomology (Rep.res f A) 1) :
    (map (MonoidHom.id H)
      (Rep.resTensorPowHeadTailIso f A n).hom (n + 2)).hom
        (restrictedIteratedCupClassSucc f A (n + 1) x) =
      cupOneAny (Rep.res f A)
        (Rep.res f (TensorPower.tensorPowObj A (n + 1))) (n + 1)
        (x 0 ⊗ₜ[k]
          restrictedIteratedCupClassSucc f A n (fun i => x i.succ)) := by
  let eTail := Rep.resTensorPowIsoSucc f
    (Iso.refl (Rep.res f A)) n
  unfold restrictedIteratedCupClassSucc
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Rep.resTensorPowIsoSucc_inv_comp_resTensorPowHeadTailIso_hom]
  rw [map_id_comp]
  simp only [ConcreteCategory.comp_apply]
  rw [iteratedCupClassSucc_headTail]
  have hnat := ConcreteCategory.congr_hom
    (cupOneAny_naturality
      (𝟙 (Rep.res f A)) eTail.inv (n + 1))
    (x 0 ⊗ₜ[k]
      iteratedCupClassSucc (Rep.res f A) n (fun i => x i.succ))
  rw [map_id] at hnat
  convert hnat using 1
  simp only [eTail, ConcreteCategory.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    ConcreteCategory.id_apply]

/-- The normalized iterated cup of restricted ambient classes followed by
one degree-one class for the source group. -/
noncomputable def restrictedIteratedCupClassSuccLastOfHom
    (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    groupCohomology
      (Rep.res f (TensorPower.tensorPowObj A (n + 1))) (n + 1) :=
  restrictedIteratedCupClassSucc f A n
    (Fin.snoc
      (fun i => groupCohomology.map f
        (𝟙 (Rep.res f A)) 1 (x i)) y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- In weight one, the normalized last-entry construction is restriction
of the ambient weight-one coefficient applied to the source-group class. -/
theorem restrictedIteratedCupClassSuccLastOfHom_zero
    (f : H →* G) (A : Rep k G)
    (x : Fin 0 → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    restrictedIteratedCupClassSuccLastOfHom f A 0
        x y =
      groupCohomology.map (MonoidHom.id H)
        ((Rep.resFunctor f).map
          (TensorPower.tensorPowObjOneIso A).inv) 1 y := by
  have hx : x = (fun i => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  rw [hx]
  unfold restrictedIteratedCupClassSuccLastOfHom
    restrictedIteratedCupClassSucc
  rw [iteratedCupClassSucc_zero]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Rep.tensorPowObjOneIso_inv_comp_resTensorPowIsoSucc_zero_inv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- At successor weight, the normalized last-entry construction exposes
the first restricted ambient class and the normalized mixed tail. -/
theorem restrictedIteratedCupClassSuccLastOfHom_succ_headTail
    (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    (map (MonoidHom.id H)
      (Rep.resTensorPowHeadTailIso f A n).hom (n + 2)).hom
        (restrictedIteratedCupClassSuccLastOfHom f A (n + 1) x y) =
      cupOneAny (Rep.res f A)
        (Rep.res f (TensorPower.tensorPowObj A (n + 1))) (n + 1)
        (groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
          restrictedIteratedCupClassSuccLastOfHom f A n
            (fun i => x i.succ) y) := by
  let z : Fin (n + 2) → groupCohomology.H1 (Rep.res f A) :=
    Fin.snoc
      (fun i => groupCohomology.map f
        (𝟙 (Rep.res f A)) 1 (x i)) y
  have hz0 : z 0 = groupCohomology.map f
      (𝟙 (Rep.res f A)) 1 (x 0) := by
    simp [z]
  have hztail : (fun i => z i.succ) =
      Fin.snoc
        (fun i => groupCohomology.map f
          (𝟙 (Rep.res f A)) 1 (x i.succ)) y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [z]
    · change Fin.snoc
          (α := fun _ => groupCohomology.H1 (Rep.res f A))
          (fun i => groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x i)) y
          j.succ.castSucc = _
      rw [Fin.snoc_castSucc]
      rw [Fin.snoc_castSucc]
  unfold restrictedIteratedCupClassSuccLastOfHom
  change (map (MonoidHom.id H)
      (Rep.resTensorPowHeadTailIso f A n).hom (n + 2)).hom
        (restrictedIteratedCupClassSucc f A (n + 1) z) = _
  rw [restrictedIteratedCupClassSucc_headTail, hz0, hztail]

end groupCohomology
