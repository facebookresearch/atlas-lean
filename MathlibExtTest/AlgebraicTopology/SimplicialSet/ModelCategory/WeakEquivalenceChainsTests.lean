/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceChains
import Mathlib.Data.Matrix.Mul

/-!
# Chain invariance for arbitrary simplicial weak equivalences

These owner tests exercise the exact two-name public API on empty,
disconnected, representable, non-Kan, circle, and anodyne examples.  They
also enforce the explicit realization-weak premise, arbitrary Ring module
coefficients, coefficient naturality, universe polymorphism, and the absence
of any converse.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace WeakEquivalenceChainsTests

section PublicContract

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)
  {X Y : SSet.{u}} {f : X ⟶ Y}

example (hf : SSet.realizationWeakEquivalences f) :
    QuasiIso (SSet.chainComplexMap f A) :=
  SSet.realizationWeakEquivalences.quasiIso_chainComplexMap hf A

example (hf : SSet.realizationWeakEquivalences f) :
    QuasiIso (SSet.normalizedChainComplexMap f A) :=
  SSet.realizationWeakEquivalences.quasiIso_normalizedChainComplexMap hf A

end PublicContract

section BasicObjects

private abbrev basicEmptySSet : SSet.{u} :=
  (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)

example : QuasiIso
    (SSet.normalizedChainComplexMap (𝟙 basicEmptySSet.{u}) A) :=
  SSet.realizationWeakEquivalences.quasiIso_normalizedChainComplexMap
    (SSet.realizationWeakEquivalences.of_isIso (𝟙 basicEmptySSet.{u})) A

example : QuasiIso
    (SSet.chainComplexMap (𝟙 (Δ[0] : SSet.{u})) A) :=
  SSet.realizationWeakEquivalences.quasiIso_chainComplexMap
    (SSet.realizationWeakEquivalences.of_isIso (𝟙 (Δ[0] : SSet.{u}))) A

/-- The theorem applies to a non-Kan source without installing any Kan
instance on that source. -/
example : QuasiIso
    (SSet.chainComplexMap (𝟙 (Δ[1] : SSet.{u})) A) :=
  SSet.realizationWeakEquivalences.quasiIso_chainComplexMap
    (SSet.realizationWeakEquivalences.of_isIso (𝟙 (Δ[1] : SSet.{u}))) A

end BasicObjects

section Disconnected

private abbrev disconnectedTwoPointSSet : SSet.{0} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{0} (Fin 2))

private def swapTwo : ULift.{0} (Fin 2) ≃ ULift.{0} (Fin 2) :=
  Equiv.ulift.trans ((Equiv.swap 0 1).trans Equiv.ulift.symm)

private def disconnectedSwapIso :
    disconnectedTwoPointSSet ≅ disconnectedTwoPointSSet :=
  NatIso.ofComponents (fun _ ↦ swapTwo.toIso) (fun _ ↦ rfl)

private abbrev disconnectedSwap :
    disconnectedTwoPointSSet ⟶ disconnectedTwoPointSSet :=
  disconnectedSwapIso.hom

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)

example : QuasiIso
    (SSet.normalizedChainComplexMap disconnectedSwap A) :=
  SSet.realizationWeakEquivalences.quasiIso_normalizedChainComplexMap
    (SSet.realizationWeakEquivalences.of_isIso disconnectedSwap) A

example {R : Type} [Ring R] (A : ModuleCat.{0} R) : QuasiIso
    (SSet.normalizedChainComplexMap (𝟙 SSet.S1) A) :=
  SSet.realizationWeakEquivalences.quasiIso_normalizedChainComplexMap
    (SSet.realizationWeakEquivalences.of_isIso (𝟙 SSet.S1)) A

end Disconnected

section AnodyneControl

private theorem anodyne_mem_realizationWeakEquivalences
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : SSet.anodyneExtensions f) :
    SSet.realizationWeakEquivalences f := by
  rw [SSet.mem_realizationWeakEquivalences_iff]
  apply (TopCat.mem_weakHomotopyEquivalences_iff _).mp
  apply TopCat.horn_llp_le_weakHomotopyEquivalences
  rw [SSet.anodyneExtensions_eq_llp_rlp] at hf
  intro X Y p hp
  exact (sSetTopAdj.hasLiftingProperty_iff f p).mpr
    (hf _ ((TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp hp))

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)

example : QuasiIso
    (SSet.chainComplexMap
      (SSet.horn (n := 2) (1 : Fin 3)).ι A) :=
  SSet.realizationWeakEquivalences.quasiIso_chainComplexMap
    (anodyne_mem_realizationWeakEquivalences
      (SSet.anodyneExtensions.horn_ι (1 : Fin 3))) A

end AnodyneControl

section PremiseAndConverseGates

private abbrev gateEmptySSet : SSet.{0} :=
  (⊥ : (Δ[0] : SSet.{0}).Subcomplex)

private noncomputable def emptyToPoint :
    gateEmptySSet ⟶ (Δ[0] : SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.from gateEmptySSet

private abbrev gateTwoPointSSet : SSet.{0} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{0} (Fin 2))

private noncomputable def disconnectedFold :
    gateTwoPointSSet ⟶ (Δ[0] : SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.from gateTwoPointSSet

private theorem bijective_mapπ₀_of_realizationWeakEquivalence
    {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) :
    Function.Bijective (SSet.mapπ₀ f) := by
  let G : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet
  have hG : Function.Bijective (SSet.mapπ₀ (G.map f)) :=
    ((SSet.mem_realizationWeakEquivalences_iff f).mp hf).bijective_mapπ₀
  have hX : Function.Bijective
      (SSet.mapπ₀ (sSetTopAdj.unit.app X)) :=
    SSet.bijective_mapπ₀_sSetTopAdj_unit_app X
  have hY : Function.Bijective
      (SSet.mapπ₀ (sSetTopAdj.unit.app Y)) :=
    SSet.bijective_mapπ₀_sSetTopAdj_unit_app Y
  have hNat :
      f ≫ sSetTopAdj.unit.app Y =
        sSetTopAdj.unit.app X ≫ G.map f := by
    simpa only [G, Functor.id_obj, Functor.id_map] using
      sSetTopAdj.unit.naturality f
  have hMapEq :
      SSet.mapπ₀ (sSetTopAdj.unit.app Y) ∘ SSet.mapπ₀ f =
        SSet.mapπ₀ (G.map f) ∘
          SSet.mapπ₀ (sSetTopAdj.unit.app X) := by
    funext q
    change SSet.mapπ₀ (sSetTopAdj.unit.app Y) (SSet.mapπ₀ f q) =
      SSet.mapπ₀ (G.map f)
        (SSet.mapπ₀ (sSetTopAdj.unit.app X) q)
    rw [← SSet.mapπ₀_comp_apply, ← SSet.mapπ₀_comp_apply, hNat]
  have hComposite : Function.Bijective
      (SSet.mapπ₀ (sSetTopAdj.unit.app Y) ∘ SSet.mapπ₀ f) := by
    rw [hMapEq]
    exact hG.comp hX
  exact (Function.Bijective.of_comp_iff' hY (SSet.mapπ₀ f)).mp
    hComposite

private theorem emptyToPoint_mapπ₀_not_surjective :
    ¬ Function.Surjective (SSet.mapπ₀ emptyToPoint) := by
  intro h
  let y : (Δ[0] : SSet.{0}).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
    SSet.stdSimplex.obj₀Equiv.symm 0
  obtain ⟨q, _⟩ := h (SSet.π₀.mk y)
  obtain ⟨x, _⟩ := q.mk_surjective
  have hx := x.property
  change x.val ∈
    (⊥ : (Δ[0] : SSet.{0}).Subcomplex).obj
      (Opposite.op (SimplexCategory.mk 0)) at hx
  simp only [Subfunctor.bot_obj, Set.mem_empty_iff_false] at hx

private theorem gateTwoPoint_mk_injective :
    Function.Injective (SSet.π₀.mk (X := gateTwoPointSSet)) := by
  intro x y h
  rw [SSet.π₀.mk_eq_mk_iff] at h
  induction h with
  | rel x y h =>
      obtain ⟨e⟩ := h
      simpa [gateTwoPointSSet] using e.src_eq.symm.trans e.tgt_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem disconnectedFold_mapπ₀_not_injective :
    ¬ Function.Injective (SSet.mapπ₀ disconnectedFold) := by
  intro h
  let x : ULift.{0} (Fin 2) := ULift.up 0
  let y : ULift.{0} (Fin 2) := ULift.up 1
  have hxy : x ≠ y := by
    intro hxy
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down hxy)
  have hmk : SSet.π₀.mk (X := gateTwoPointSSet) x ≠
      SSet.π₀.mk (X := gateTwoPointSSet) y :=
    fun hmk ↦ hxy (gateTwoPoint_mk_injective hmk)
  apply hmk
  apply h
  simp only [SSet.mapπ₀_mk]
  apply congrArg SSet.π₀.mk
  apply SSet.stdSimplex.obj₀Equiv.injective
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

example : ¬ SSet.realizationWeakEquivalences emptyToPoint := by
  intro hf
  exact emptyToPoint_mapπ₀_not_surjective
    (bijective_mapπ₀_of_realizationWeakEquivalence hf).surjective

example : ¬ SSet.realizationWeakEquivalences disconnectedFold := by
  intro hf
  exact disconnectedFold_mapπ₀_not_injective
    (bijective_mapπ₀_of_realizationWeakEquivalence hf).injective

variable {R : Type u} [Ring R]

/-- Zero coefficients are supported but do not provide a converse. -/
example : QuasiIso
    (SSet.normalizedChainComplexMap (𝟙 (Δ[0] : SSet.{u}))
      (⊥_ (ModuleCat.{u} R))) :=
  SSet.realizationWeakEquivalences.quasiIso_normalizedChainComplexMap
    (SSet.realizationWeakEquivalences.of_isIso (𝟙 (Δ[0] : SSet.{u})))
    (⊥_ (ModuleCat.{u} R))

/-- error: Unknown constant
`SSet.realizationWeakEquivalences.of_quasiIso_chainComplexMap` -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_quasiIso_chainComplexMap

end PremiseAndConverseGates

section NoncommutativeCoefficients

private abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

example : True := by
  fail_if_success let _ : CommRing MatrixRing := inferInstance
  trivial

example : QuasiIso
    (SSet.chainComplexMap (𝟙 (Δ[0] : SSet.{0}))
      (ModuleCat.of MatrixRing MatrixRing)) :=
  SSet.realizationWeakEquivalences.quasiIso_chainComplexMap
    (SSet.realizationWeakEquivalences.of_isIso (𝟙 (Δ[0] : SSet.{0})))
    (ModuleCat.of MatrixRing MatrixRing)

end NoncommutativeCoefficients

section CoefficientNaturality

variable {R S : ModuleCat.{u} ℤ} (a : R ⟶ S)
  {X Y : SSet.{u}} (f : X ⟶ Y)

example :
    SSet.chainComplexMap f R ≫
        ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).map a).app Y =
      ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).map a).app X ≫
        SSet.chainComplexMap f S :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).map a).naturality f

example :
    SSet.normalizedChainComplexMap f R ≫
        ((SSet.normalizedChainComplexFunctor
          (C := ModuleCat.{u} ℤ)).map a).app Y =
      ((SSet.normalizedChainComplexFunctor
        (C := ModuleCat.{u} ℤ)).map a).app X ≫
        SSet.normalizedChainComplexMap f S :=
  ((SSet.normalizedChainComplexFunctor
    (C := ModuleCat.{u} ℤ)).map a).naturality f

end CoefficientNaturality

section ExplicitUniverses

example {R : Type 1} [Ring R] (A : ModuleCat.{1} R)
    {X Y : SSet.{1}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) :
    QuasiIso (SSet.chainComplexMap f A) :=
  SSet.realizationWeakEquivalences.quasiIso_chainComplexMap hf A

example {R : Type} [Ring R] (A : ModuleCat.{0} R)
    {X Y : SSet.{0}} {f : X ⟶ Y}
    (hf : SSet.realizationWeakEquivalences f) :
    QuasiIso (SSet.normalizedChainComplexMap f A) :=
  SSet.realizationWeakEquivalences.quasiIso_normalizedChainComplexMap hf A

end ExplicitUniverses

#print axioms SSet.realizationWeakEquivalences.quasiIso_chainComplexMap
#print axioms SSet.realizationWeakEquivalences.quasiIso_normalizedChainComplexMap

end WeakEquivalenceChainsTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
