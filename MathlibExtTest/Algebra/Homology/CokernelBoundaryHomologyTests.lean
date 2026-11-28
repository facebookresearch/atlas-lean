/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.HomologicalComplexCokernelHomology
public import MathlibExt.Algebra.Homology.HomologicalComplexImageCokernel
public import MathlibExt.Algebra.Homology.HomologicalComplexModuleCokernel
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Tactic.NormNum

/-!
# Cokernel homology at the nonnegative boundary

The zero-differential complex with an integer module in every nonnegative degree has a map
which is the identity in degree one and zero elsewhere. Its degree-zero cokernel homology
comparison applies even though the next positive component of the map is nonzero. A second
map supported in degree two tests the degree-one comparison with zero components in degrees
zero and one.

The homology classes represented by one remain nonzero under the canonical cokernel
projections and the image/coimage quotient comparisons. The component quotient coordinate is
also tested directly on the integer one.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace MathlibExtTest.CokernelBoundaryHomology

private abbrev E := ModuleCat.{0} ℤ
private abbrev N : E := ModuleCat.of ℤ ℤ

private abbrev K : ChainComplex E ℕ :=
  ChainComplex.of (fun _ => N) (fun _ => 0) (by intro n; simp)

private theorem differential_zero (i j : ℕ) : K.d i j = 0 := by
  simp [K, ChainComplex.of.d]

private def spike (k : ℕ) : K ⟶ K :=
  ChainComplex.ofHom (fun n => if n = k then 𝟙 N else 0) (by
    intro n
    rw [differential_zero, differential_zero]
    simp)

private theorem spike_at (k : ℕ) : (spike k).f k = 𝟙 N := by simp [spike]

private theorem spike_away (k n : ℕ) (h : n ≠ k) : (spike k).f n = 0 := by
  simp [spike, h]

private def coordinate (n : ℕ) : K.homology n ≅ N :=
  (ShortComplex.HomologyData.ofZeros (K.sc n)
    (differential_zero _ _) (differential_zero _ _)).left.homologyIso

private def oneClass (n : ℕ) : K.homology n := (coordinate n).inv.hom 1

private theorem oneClass_ne_zero (n : ℕ) : oneClass n ≠ 0 := by
  intro h
  have hc := congrArg (coordinate n).hom.hom h
  change (coordinate n).hom.hom ((coordinate n).inv.hom 1) = _ at hc
  rw [ModuleCat.hom_inv_apply, map_zero] at hc
  norm_num at hc

private def zeroComparison : K.homology 0 ≅ (cokernel (spike 1)).homology 0 :=
  cokernelHomologyZeroIso (spike 1) (spike_away 1 0 (by decide))

private def oneComparison : K.homology 1 ≅ (cokernel (spike 2)).homology 1 :=
  cokernelHomologyOneIso (spike 2)
    (spike_away 2 1 (by decide)) (spike_away 2 0 (by decide))

example : (spike 1).f 0 = 0 ∧ (spike 1).f 1 ≠ 0 := by
  constructor
  · exact spike_away 1 0 (by decide)
  · intro h
    have hc := congrArg (fun f : N ⟶ N => f.hom 1) h
    rw [spike_at] at hc
    change (1 : ℤ) = 0 at hc
    norm_num at hc

example : zeroComparison.hom = homologyMap (cokernel.π (spike 1)) 0 := by
  simpa only [zeroComparison, cokernelHomologyZeroIso] using
    cokernelHomologyIsoOfZeroComponents_hom (spike 1) 0
      (spike_away 1 0 (by decide)) (by
        erw [ChainComplex.next_nat_zero]
        exact spike_away 1 0 (by decide))

private theorem zeroComparison_one_ne_zero : (zeroComparison.hom).hom (oneClass 0) ≠ 0 := by
  intro h
  have hc := congrArg zeroComparison.inv.hom h
  rw [ModuleCat.inv_hom_apply, map_zero] at hc
  exact oneClass_ne_zero 0 hc

example : (zeroComparison.hom).hom (oneClass 0) ≠ 0 := zeroComparison_one_ne_zero

example : (spike 2).f 1 = 0 ∧ (spike 2).f 0 = 0 ∧ (spike 2).f 2 ≠ 0 := by
  refine ⟨spike_away 2 1 (by decide), spike_away 2 0 (by decide), ?_⟩
  intro h
  have hc := congrArg (fun f : N ⟶ N => f.hom 1) h
  rw [spike_at] at hc
  change (1 : ℤ) = 0 at hc
  norm_num at hc

example : oneComparison.hom = homologyMap (cokernel.π (spike 2)) 1 := by
  simpa only [oneComparison, cokernelHomologyOneIso] using
    cokernelHomologyIsoOfZeroComponents_hom (spike 2) 1
      (spike_away 2 1 (by decide)) (by
        erw [ChainComplex.next_nat_succ (0 : ℕ)]
        exact spike_away 2 0 (by decide))

example : (oneComparison.hom).hom (oneClass 1) ≠ 0 := by
  intro h
  have hc := congrArg oneComparison.inv.hom h
  rw [ModuleCat.inv_hom_apply, map_zero] at hc
  exact oneClass_ne_zero 1 hc

example :
    (imageCokernelHomologyIso (spike 1) 0).hom.hom
        ((homologyMap (cokernel.π (Abelian.image.ι (spike 1))) 0).hom (oneClass 0)) =
      (homologyMap (cokernel.π (spike 1)) 0).hom (oneClass 0) :=
  ConcreteCategory.congr_hom (imageCokernelHomologyIso_projection (spike 1) 0) (oneClass 0)

example :
    (coimageCokernelHomologyIso (spike 1) 0).hom.hom
        ((homologyMap (cokernel.π (Abelian.factorThruCoimage (spike 1))) 0).hom
          (oneClass 0)) =
      (homologyMap (cokernel.π (spike 1)) 0).hom (oneClass 0) :=
  ConcreteCategory.congr_hom (coimageCokernelHomologyIso_projection (spike 1) 0) (oneClass 0)

example :
    (imageCokernelHomologyIso (spike 1) 0).hom.hom
      ((homologyMap (cokernel.π (Abelian.image.ι (spike 1))) 0).hom (oneClass 0)) ≠ 0 := by
  have h := ConcreteCategory.congr_hom
    (imageCokernelHomologyIso_projection (spike 1) 0) (oneClass 0)
  change (imageCokernelHomologyIso (spike 1) 0).hom.hom
    ((homologyMap (cokernel.π (Abelian.image.ι (spike 1))) 0).hom (oneClass 0)) =
      (homologyMap (cokernel.π (spike 1)) 0).hom (oneClass 0) at h
  rw [h]
  change zeroComparison.hom.hom (oneClass 0) ≠ 0
  exact zeroComparison_one_ne_zero

example :
    (coimageCokernelHomologyIso (spike 1) 0).hom.hom
      ((homologyMap (cokernel.π (Abelian.factorThruCoimage (spike 1))) 0).hom
        (oneClass 0)) ≠ 0 := by
  have h := ConcreteCategory.congr_hom
    (coimageCokernelHomologyIso_projection (spike 1) 0) (oneClass 0)
  change (coimageCokernelHomologyIso (spike 1) 0).hom.hom
    ((homologyMap (cokernel.π (Abelian.factorThruCoimage (spike 1))) 0).hom (oneClass 0)) =
      (homologyMap (cokernel.π (spike 1)) 0).hom (oneClass 0) at h
  rw [h]
  change zeroComparison.hom.hom (oneClass 0) ≠ 0
  exact zeroComparison_one_ne_zero

example :
    (moduleCokernelDegreeIso (spike 1) 0).hom.hom
        (((cokernel.π (spike 1)).f 0).hom 1) =
      (LinearMap.range ((spike 1).f 0).hom).mkQ 1 :=
  ConcreteCategory.congr_hom (moduleCokernelDegreeIso_projection (spike 1) 0) 1

end MathlibExtTest.CokernelBoundaryHomology
