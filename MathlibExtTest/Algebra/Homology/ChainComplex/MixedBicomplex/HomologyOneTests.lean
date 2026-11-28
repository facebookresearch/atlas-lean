/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.ChainComplex.MixedBicomplex.HomologyOne
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A nonzero degree-one class killed by the mixed boundary

The chain complex has an integer module in every nonnegative degree and zero
boundary. Its raising homotopy is the identity from degree zero to degree one
and zero elsewhere. Thus B₀=id and B²=0. The first-column map sends the nonzero
class of 1 in H₁(K) to zero in the mixed total: its additional incoming
boundary is +B₀, not its negative.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace MathlibExtTest.MixedHomologyOne

abbrev Z := ModuleCat.of ℤ ℤ

def K : ChainComplex (ModuleCat.{0} ℤ) ℕ where
  X _ := Z
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def raising : Homotopy (0 : K ⟶ K) 0 where
  hom i j := if i = 0 ∧ j = 1 then 𝟙 Z else 0
  zero i j h := by
    split_ifs with hij
    · rcases hij with ⟨rfl, rfl⟩
      exact (h rfl).elim
    · rfl
  comm i := by
    change (0 : Z ⟶ Z) = (0 : Z ⟶ Z) ≫ _ + _ ≫ (0 : Z ⟶ Z) + (0 : Z ⟶ Z)
    simp

lemma raisingSquare (n : ℕ) :
    raising.hom n (n + 1) ≫ raising.hom (n + 1) (n + 2) = 0 := by
  simp [raising]

instance : HomologicalComplex₂.HasTotal
    (ChainComplex.mixedBicomplex K raising raisingSquare) (ComplexShape.down ℕ) := by
  infer_instance

abbrev T := HomologicalComplex₂.total
  (ChainComplex.mixedBicomplex K raising raisingSquare) (ComplexShape.down ℕ)
abbrev P := K.sc' 2 1 0
abbrev S := ChainComplex.mixedHomologyOneShortComplex K raising

def sourceComparison : K.homology 1 ≅ P.homology :=
  K.homologyIsoSc' 2 1 0
    ((ComplexShape.down ℕ).prev_eq' (by rfl))
    ((ComplexShape.down ℕ).next_eq' (by rfl))

def shortClass : P.homology :=
  (P.asIsoHomologyι (by rfl)).inv (P.pOpcycles (1 : ℤ))

def sourceClass : K.homology 1 := sourceComparison.inv shortClass

lemma shortClass_nonzero : shortClass ≠ 0 := by
  intro h
  let e := P.asIsoHomologyι (by rfl)
  change e.inv (P.pOpcycles (1 : ℤ)) = 0 at h
  have hc := congrArg (fun a => e.hom a) h
  have hi := congrArg (fun f : P.opcycles ⟶ P.opcycles =>
    f (P.pOpcycles (1 : ℤ))) e.inv_hom_id
  change e.hom (e.inv (P.pOpcycles (1 : ℤ))) = P.pOpcycles (1 : ℤ) at hi
  have hp : P.pOpcycles (1 : ℤ) = 0 :=
    hi.symm.trans (hc.trans e.hom.hom.map_zero)
  have hm := (P.moduleCat_pOpcycles_eq_zero_iff (1 : ℤ)).mp hp
  change (1 : ℤ) ∈ LinearMap.range (0 : ℤ →ₗ[ℤ] ℤ) at hm
  have : (1 : ℤ) = 0 := by
    simpa only [LinearMap.range_zero, Submodule.mem_bot] using hm
  exact Int.one_ne_zero this

lemma sourceClass_nonzero : sourceClass ≠ 0 := by
  intro h
  apply shortClass_nonzero
  change sourceComparison.inv shortClass = 0 at h
  have hc := congrArg (fun a => sourceComparison.hom a) h
  have hi := congrArg (fun f : P.homology ⟶ P.homology =>
    f shortClass) sourceComparison.inv_hom_id
  change sourceComparison.hom (sourceComparison.inv shortClass) = shortClass at hi
  exact hi.symm.trans (hc.trans sourceComparison.hom.hom.map_zero)

lemma positiveBoundary :
    (biprod.desc (K.d 2 1) (raising.hom 0 1))
      ((biprod.inr : Z ⟶ Z ⊞ Z) (1 : ℤ)) = (1 : ℤ) := by
  have h := congrArg (fun f : Z ⟶ Z => f (1 : ℤ))
    (biprod.inr_desc (0 : Z ⟶ Z) (𝟙 Z))
  change (biprod.desc (0 : Z ⟶ Z) (𝟙 Z))
    ((biprod.inr : Z ⟶ Z ⊞ Z) (1 : ℤ)) = 1 at h
  exact h

lemma shortClass_killed :
    ShortComplex.homologyMap
      (ChainComplex.mixedColumnZeroShortComplexMap K raising) shortClass = 0 := by
  have hp : S.pOpcycles (1 : ℤ) = 0 := by
    apply (S.moduleCat_pOpcycles_eq_zero_iff (1 : ℤ)).mpr
    refine ⟨(biprod.inr : Z ⟶ Z ⊞ Z) (1 : ℤ), ?_⟩
    exact positiveBoundary
  have h := congrArg (fun f : Z ⟶ S.homology => f (1 : ℤ))
    (ChainComplex.mixedColumnZeroShortComplexMap_quotient K raising (by rfl))
  change ShortComplex.homologyMap
      (ChainComplex.mixedColumnZeroShortComplexMap K raising) shortClass =
    (S.asIsoHomologyι (by rfl)).inv (S.pOpcycles (1 : ℤ)) at h
  rw [hp] at h
  exact h.trans (S.asIsoHomologyι (by rfl)).inv.hom.map_zero

lemma sourceClass_killed :
    homologyMap
      (ChainComplex.mixedColumnZeroInclusion K raising raisingSquare) 1 sourceClass = 0 := by
  let e := ChainComplex.mixedHomologyOneIso K raising raisingSquare
  apply e.toLinearEquiv.injective
  have h := congrArg (fun f : K.homology 1 ⟶ S.homology => f sourceClass)
    (ChainComplex.mixedColumnZeroInclusion_homology K raising raisingSquare)
  change e.hom (homologyMap
      (ChainComplex.mixedColumnZeroInclusion K raising raisingSquare) 1 sourceClass) =
    ShortComplex.homologyMap (ChainComplex.mixedColumnZeroShortComplexMap K raising)
      (sourceComparison.hom sourceClass) at h
  have hi := congrArg (fun f : P.homology ⟶ P.homology =>
    f shortClass) sourceComparison.inv_hom_id
  change sourceComparison.hom sourceClass = shortClass at hi
  rw [hi, shortClass_killed] at h
  exact h.trans e.hom.hom.map_zero.symm

example : raising.hom 0 1 (1 : ℤ) = (1 : ℤ) := rfl

example :
    ((ChainComplex.mixedTotalTwoIso K raising raisingSquare).inv ≫ T.d 2 1 ≫
      (ChainComplex.mixedTotalOneIso K raising raisingSquare).hom)
        ((biprod.inr : Z ⟶ Z ⊞ Z) (1 : ℤ)) = (1 : ℤ) := by
  have h := congrArg (fun f : Z ⊞ Z ⟶ Z =>
    f ((biprod.inr : Z ⟶ Z ⊞ Z) (1 : ℤ)))
    (ChainComplex.mixedTotalTwoIso_inv_d K raising raisingSquare)
  exact h.trans positiveBoundary

example : sourceClass ≠ 0 := sourceClass_nonzero

example : homologyMap
    (ChainComplex.mixedColumnZeroInclusion K raising raisingSquare) 1 sourceClass = 0 :=
  sourceClass_killed

end MathlibExtTest.MixedHomologyOne
