/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Products

/-!
# Tests for native products of compactly generated weak Hausdorff spaces
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace MathlibExtTest.CGWH.ProductsTests

section PublicSurface

#check CGWH.piObj
#check CGWH.piπ
#check CGWH.piFan
#check CGWH.piFanIsLimit
#check CGWH.piIsoPi
#check CGWH.piComparisonToTop
#check CGWH.piComparisonToTop_apply
#check CGWH.piComparisonToTop_generic_coherence
#check CGWH.piComparisonToTop_isHomeomorph_iff
#check CGWH.piComparisonToTop_isHomeomorph_of_firstCountable
#check CGWH.prodComparisonToTop
#check CGWH.prodComparisonToTop_fst
#check CGWH.prodComparisonToTop_snd
#check CGWH.prodComparisonToTop_bijective
#check CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_left
#check CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_right
#check CGWH.prodComparisonToTop_isHomeomorph_of_firstCountable
#check CGWH.instHasProducts
#check CGWH.instHasFiniteProducts

end PublicSurface

section Instances

example : (inferInstance : HasProducts.{v} CGWH.{u, v}) =
    CGWH.instHasProducts := rfl

example : (inferInstance : HasFiniteProducts CGWH.{u, v}) =
    CGWH.instHasFiniteProducts := rfl

example : CGWH.instHasFiniteProducts =
    hasFiniteProducts_of_hasProducts.{v, v, v + 1} CGWH.{u, v} := rfl

example : HasProducts.{0} CGWH.{0, 0} := inferInstance
example : HasFiniteProducts CGWH.{0, 0} := inferInstance
example : HasProducts.{1} CGWH.{1, 1} := inferInstance
example : HasFiniteProducts CGWH.{1, 1} := inferInstance
example : HasProducts.{1} CGWH.{0, 1} := inferInstance
example : HasFiniteProducts CGWH.{0, 1} := inferInstance
example : HasProducts.{0} CGWH.{1, 0} := inferInstance
example : HasFiniteProducts CGWH.{1, 0} := inferInstance

example : (inferInstance : HasProducts.{0} CGWH.{0, 0}) =
    CGWH.instHasProducts := rfl

example : (inferInstance : HasFiniteProducts CGWH.{0, 0}) =
    CGWH.instHasFiniteProducts := rfl

example : True := by
  let direct : HasProductsOfShape WalkingPair CGWH.{0, 0} :=
    hasProductsOfShape_of_hasProducts WalkingPair
  let finite : HasProductsOfShape WalkingPair CGWH.{0, 0} := inferInstance
  have : direct = finite := Subsingleton.elim _ _
  trivial

end Instances

section ArbitraryProducts

variable {I : Type v} (X : I → CGWH.{u, v})

example : CGWH.{u, v} := CGWH.piObj X

example (i : I) : CGWH.piObj X ⟶ X i := CGWH.piπ X i

example : IsLimit (CGWH.piFan X) := CGWH.piFanIsLimit X

example (s : Fan X) (i : I) :
    (CGWH.piFanIsLimit X).lift s ≫ CGWH.piπ X i = s.proj i :=
  (CGWH.piFanIsLimit X).fac s ⟨i⟩

example (s : Fan X) (m : s.pt ⟶ CGWH.piObj X)
    (hm : ∀ i, m ≫ CGWH.piπ X i = s.proj i) :
    m = (CGWH.piFanIsLimit X).lift s := by
  apply (CGWH.piFanIsLimit X).uniq s
  rintro ⟨i⟩
  exact hm i

example (i : I) :
    (CGWH.piIsoPi X).hom ≫ CGWH.piπ X i = Pi.π X i :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) (CGWH.piFanIsLimit X) ⟨i⟩

example (x : CGWH.piObj X) : CGWH.piComparisonToTop X x = x :=
  CGWH.piComparisonToTop_apply X x

example :
    CGWH.cgwhToTop.map (CGWH.piIsoPi X).hom ≫
        CGWH.piComparisonToTop X =
      Limits.piComparison CGWH.cgwhToTop X ≫
        (TopCat.piIsoPi (fun i => CGWH.cgwhToTop.obj (X i))).hom :=
  CGWH.piComparisonToTop_generic_coherence X

end ArbitraryProducts

section EmptyProduct

private abbrev E : ULift.{v} Empty → CGWH.{u, v} :=
  fun i => nomatch i.down

example : IsTerminal (CGWH.piObj E) :=
  (isLimitEquivIsTerminalOfIsEmpty CGWH.{u, v} (CGWH.piFan E))
    (CGWH.piFanIsLimit E)

example : CGWH.piObj E ≅ ⊤_ CGWH.{u, v} :=
  ((isLimitEquivIsTerminalOfIsEmpty CGWH.{u, v} (CGWH.piFan E))
    (CGWH.piFanIsLimit E)).uniqueUpToIso terminalIsTerminal

example : IsHomeomorph (CGWH.piComparisonToTop E) := by
  let _ : ∀ i, FirstCountableTopology (E i) :=
    fun i => nomatch i.down
  exact CGWH.piComparisonToTop_isHomeomorph_of_firstCountable E

end EmptyProduct

section SingletonProduct

variable (X : CGWH.{u, v})
private abbrev P (X : CGWH.{u, v}) :
    ULift.{v, 0} PUnit.{1} → CGWH.{u, v} :=
  fun _ => X

private noncomputable def singletonFan (X : CGWH.{u, v}) : Fan (P.{u, v} X) :=
  Fan.mk (P.{u, v} X (ULift.up.{v, 0} PUnit.unit.{1})) (fun _ => 𝟙 X)

private noncomputable def singletonLift (X : CGWH.{u, v}) :
    P.{u, v} X (ULift.up.{v, 0} PUnit.unit.{1}) ⟶
      CGWH.piObj (P.{u, v} X) :=
  (CGWH.piFanIsLimit (P.{u, v} X)).lift (singletonFan.{u, v} X)

example : singletonLift.{u, v} X ≫
    CGWH.piπ (P.{u, v} X) (ULift.up.{v, 0} PUnit.unit.{1}) = 𝟙 X :=
  (CGWH.piFanIsLimit (P.{u, v} X)).fac (singletonFan.{u, v} X)
    ⟨ULift.up.{v, 0} PUnit.unit.{1}⟩

example : CGWH.piπ (P.{u, v} X) (ULift.up.{v, 0} PUnit.unit.{1}) ≫
    singletonLift.{u, v} X = 𝟙 _ := by
  apply (CGWH.piFanIsLimit (P.{u, v} X)).hom_ext
  rintro ⟨i⟩
  obtain rfl : i = ULift.up.{v, 0} PUnit.unit.{1} := Subsingleton.elim _ _
  have hfac := (CGWH.piFanIsLimit (P.{u, v} X)).fac
    (singletonFan.{u, v} X) ⟨ULift.up.{v, 0} PUnit.unit.{1}⟩
  unfold singletonFan at hfac
  unfold singletonLift singletonFan
  dsimp only [P] at *
  rw [Category.assoc, hfac, Category.id_comp]
  change CGWH.piπ (P.{u, v} X) (ULift.up.{v, 0} PUnit.unit.{1}) ≫
      𝟙 X = CGWH.piπ (P.{u, v} X) (ULift.up.{v, 0} PUnit.unit.{1})
  rw [Category.comp_id]

example : IsIso
    (CGWH.piπ (P.{u, v} X) (ULift.up.{v, 0} PUnit.unit.{1})) :=
  ⟨⟨singletonLift.{u, v} X,
    by
      apply (CGWH.piFanIsLimit (P.{u, v} X)).hom_ext
      rintro ⟨i⟩
      obtain rfl : i = ULift.up.{v, 0} PUnit.unit.{1} := Subsingleton.elim _ _
      have hfac := (CGWH.piFanIsLimit (P.{u, v} X)).fac
        (singletonFan.{u, v} X) ⟨ULift.up.{v, 0} PUnit.unit.{1}⟩
      unfold singletonFan at hfac
      unfold singletonLift singletonFan
      dsimp only [P] at *
      rw [Category.assoc, hfac, Category.id_comp]
      change CGWH.piπ (P.{u, v} X) (ULift.up.{v, 0} PUnit.unit.{1}) ≫
          𝟙 X = CGWH.piπ (P.{u, v} X) (ULift.up.{v, 0} PUnit.unit.{1})
      rw [Category.comp_id],
    (CGWH.piFanIsLimit (P.{u, v} X)).fac (singletonFan.{u, v} X)
      ⟨ULift.up.{v, 0} PUnit.unit.{1}⟩⟩⟩

example : IsHomeomorph (CGWH.piComparisonToTop (P.{u, v} X)) := by
  let probes := CompactlyGenerated.compactHausProbes.{u}
  have hX : IsGeneratedBy probes X :=
    isGeneratedBy_compactHausProbes_iff.2 inferInstance
  let _ : IsGeneratedBy probes X := hX
  have hPi : IsGeneratedBy probes (∀ _ : ULift.{v, 0} PUnit.{1}, X) :=
    (Homeomorph.piUnique (fun _ : ULift.{v, 0} PUnit.{1} => X)).symm.isQuotientMap.isGeneratedBy
  apply (CGWH.piComparisonToTop_isHomeomorph_iff (P.{u, v} X)).2
  exact isGeneratedBy_compactHausProbes_iff.1 hPi

end SingletonProduct

section BinaryProducts

variable (X Y : CGWH.{u, v})

example : CGWH.cgwhToTop.obj (X ⨯ Y) ⟶ TopCat.of (X × Y) :=
  CGWH.prodComparisonToTop X Y

example : CGWH.prodComparisonToTop X Y ≫ TopCat.prodFst =
    CGWH.cgwhToTop.map (Limits.prod.fst : X ⨯ Y ⟶ X) :=
  CGWH.prodComparisonToTop_fst X Y

example : CGWH.prodComparisonToTop X Y ≫ TopCat.prodSnd =
    CGWH.cgwhToTop.map (Limits.prod.snd : X ⨯ Y ⟶ Y) :=
  CGWH.prodComparisonToTop_snd X Y

example : Function.Bijective (CGWH.prodComparisonToTop X Y) :=
  CGWH.prodComparisonToTop_bijective X Y

example [LocallyCompactSpace X] [T2Space X] :
    IsHomeomorph (CGWH.prodComparisonToTop X Y) :=
  CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_left X Y

example [LocallyCompactSpace Y] [T2Space Y] :
    IsHomeomorph (CGWH.prodComparisonToTop X Y) :=
  CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_right X Y

example [FirstCountableTopology X] [FirstCountableTopology Y] :
    IsHomeomorph (CGWH.prodComparisonToTop X Y) :=
  CGWH.prodComparisonToTop_isHomeomorph_of_firstCountable X Y

end BinaryProducts

section CountableProducts

variable (X : ULift.{v} ℕ → CGWH.{u, v})
  [∀ n, FirstCountableTopology (X n)]

example : IsHomeomorph (CGWH.piComparisonToTop X) :=
  CGWH.piComparisonToTop_isHomeomorph_of_firstCountable X

end CountableProducts

section MissingInstances

section WithoutProducts

attribute [-instance] CGWH.instHasProducts

example : True := by
  fail_if_success
    let _ : HasProducts.{v} CGWH.{u, v} := inferInstance
  trivial

end WithoutProducts

section WithoutFiniteProducts

attribute [-instance] CGWH.instHasFiniteProducts

example : True := by
  fail_if_success
    let _ : HasFiniteProducts CGWH.{u, v} := inferInstance
  trivial

end WithoutFiniteProducts

end MissingInstances

section Negative

example : True := by
  fail_if_success
    let _ : CartesianMonoidalCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : MonoidalClosed CGWH.{u, v} := inferInstance
  trivial

#guard_msgs (error, substring := true) in
#check CGWH.walkingPairPiHomeomorphProd

#guard_msgs (error, substring := true) in
#check CGWH.walkingPairPiHomeomorphProd_apply_left

#guard_msgs (error, substring := true) in
#check CGWH.walkingPairPiHomeomorphProd_apply_right

end Negative

#print axioms CGWH.piObj
#print axioms CGWH.piπ
#print axioms CGWH.piFan
#print axioms CGWH.piFanIsLimit
#print axioms CGWH.instHasProducts
#print axioms CGWH.instHasFiniteProducts
#print axioms CGWH.piIsoPi
#print axioms CGWH.piComparisonToTop
#print axioms CGWH.piComparisonToTop_apply
#print axioms CGWH.piComparisonToTop_generic_coherence
#print axioms CGWH.piComparisonToTop_isHomeomorph_iff
#print axioms CGWH.piComparisonToTop_isHomeomorph_of_firstCountable
#print axioms CGWH.prodComparisonToTop
#print axioms CGWH.prodComparisonToTop_fst
#print axioms CGWH.prodComparisonToTop_snd
#print axioms CGWH.prodComparisonToTop_bijective
#print axioms CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_left
#print axioms CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_right
#print axioms CGWH.prodComparisonToTop_isHomeomorph_of_firstCountable

end MathlibExtTest.CGWH.ProductsTests
