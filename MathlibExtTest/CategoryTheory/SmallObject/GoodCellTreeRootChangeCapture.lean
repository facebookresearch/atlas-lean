/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RootChangeCapture
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeRootChangeColimits

import Lean.Elab.Tactic.Omega

/-!
# Original different-root capture with infinite coefficients and nonmonomorphic maps

The original one-fold quotient under Nat is relatively presentable and
has an infinite underlying chosen quotient. Its constant map to the empty
PUnit-root tree factors through that tree's same bounded presentation,
although every mapped piece is nonpresentable under Nat. A finite family
has different original source roots and seeds. Distinct original free-source
maps into the empty Nat piece become equal on a genuine larger support.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  BoundedLowerSupport RootChangeCapture

namespace RootChangeCaptureExamples

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The original predecessor function, agreeing on the two folded original root values. -/
def originalPredecessor : ℕ ⟶ ℕ := ↾fun k => k - 1

theorem originalPredecessorCondition :
    GoodCellTreeDataExamples.attachNat ≫ originalPredecessor =
      GoodCellTreeDataExamples.fold ≫ (↾fun _ => (0 : ℕ)) := by
  ext i
  change i.val - 1 = 0
  have hi : i.val < 2 := i.isLt
  omega

/-- The actual original pushout descender on the same chosen one-fold quotient. -/
def originalQuotientDesc : pushout GoodCellTreeDataExamples.attachNat
    GoodCellTreeDataExamples.fold ⟶ ℕ :=
  pushout.desc originalPredecessor (↾fun _ => (0 : ℕ)) originalPredecessorCondition

theorem originalQuotientDesc_root :
    GoodCellTreeDataExamples.quotientArrow ≫ originalQuotientDesc = originalPredecessor :=
  pushout.inl_desc _ _ _

theorem originalQuotientDesc_cell :
    GoodCellTreeDataExamples.quotientCell ≫ originalQuotientDesc = (↾fun _ => (0 : ℕ)) :=
  pushout.inr_desc _ _ _

/-- The original quotient images at n+2, with no replacement of the chosen quotient type. -/
def originalQuotientInjection (n : ℕ) :
    pushout GoodCellTreeDataExamples.attachNat GoodCellTreeDataExamples.fold :=
  GoodCellTreeDataExamples.quotientArrow (n + 2)

theorem originalQuotientDesc_injection (n : ℕ) :
    originalQuotientDesc (originalQuotientInjection n) = n + 1 := by
  have h := ConcreteCategory.congr_hom originalQuotientDesc_root (n + 2)
  change originalQuotientDesc (originalQuotientInjection n) = n + 2 - 1 at h
  have he : n + 2 - 1 = n + 1 := by omega
  exact h.trans he

/-- Evaluating the original descender proves the genuine injection of Nat into this quotient. -/
theorem originalQuotientInjection_injective : Function.Injective originalQuotientInjection := by
  intro n m he
  have h := congrArg originalQuotientDesc he
  rw [originalQuotientDesc_injection, originalQuotientDesc_injection] at h
  change n + 1 = m + 1 at h
  exact Nat.add_right_cancel h

/-- The original chosen one-fold coefficient type is genuinely infinite. -/
instance originalQuotientInfinite :
    Infinite (pushout GoodCellTreeDataExamples.attachNat GoodCellTreeDataExamples.fold) :=
  Infinite.of_injective originalQuotientInjection originalQuotientInjection_injective

/-- Its actual cardinal is at least aleph0, witnessed by the same original injection. -/
theorem originalQuotientCardinalLowerBound :
    Cardinal.aleph0.{0} ≤
      Cardinal.mk (pushout GoodCellTreeDataExamples.attachNat GoodCellTreeDataExamples.fold) := by
  simpa only [Cardinal.mk_nat] using Cardinal.mk_le_of_injective originalQuotientInjection_injective

/-- The original relatively compact source's underlying coefficient is NOT compact at that rank. -/
theorem originalCoefficientNotPresentable :
    ¬ IsCardinalPresentable GoodCellTreeDataExamples.quotientTree.{t}.endpointObj.right
      Cardinal.aleph0.{0} := by
  intro h
  have hSize := (Types.isCardinalPresentable_iff Cardinal.aleph0.{0}).1 h
  have hlt := (hasCardinalLT_iff_cardinal_mk_lt _ Cardinal.aleph0.{0}).1 hSize
  exact (not_lt_of_ge originalQuotientCardinalLowerBound) hlt

/-- The actual same source is compact relative to its original Nat root. -/
theorem originalSourcePresentable :
    IsCardinalPresentable GoodCellTreeDataExamples.quotientTree.{t}.endpointObj
      Cardinal.aleph0.{0} :=
  RelativeCellPresentabilityExamples.originalEndpointPresentable.{t}

/-- The original raw map sends that exact chosen quotient to the actual unit endpoint. -/
def originalQuotientToUnit : GoodCellTreeDataExamples.quotientTree.{t}.endpointObj.right ⟶
    RootChangeColimitExamples.unitTree.{t}.endpointObj.right := ↾fun _ => PUnit.unit

theorem originalQuotientToUnit_root :
    GoodCellTreeDataExamples.quotientTree.{t}.hom ≫ originalQuotientToUnit.{t} =
      RootChangeColimitExamples.originalRoot ≫ RootChangeColimitExamples.unitTree.{t}.hom := by
  ext n
  rfl

/-- Empty original labels make each bounded support the same full lower support. -/
theorem originalEmptySupport_full
    (B : Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0}) :
    B.1 = ⊤ := by
  ext a
  exact isEmptyElim a

/-- Keep the original empty-tree endpoint Iso in the comparison of every mapped piece. -/
def originalMappedEmptyPieceIso
    (B : Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0}) :
    (Under.map RootChangeColimitExamples.originalRoot).obj
        (RootChangeColimitExamples.unitTree.{t}.lowerData.obj B.1) ≅
      (Under.map RootChangeColimitExamples.originalRoot).obj
        RootChangeColimitExamples.unitTree.{t}.endpointObj :=
  (Under.map RootChangeColimitExamples.originalRoot).mapIso
    (eqToIso (congrArg RootChangeColimitExamples.unitTree.{t}.lowerData.obj
      (originalEmptySupport_full B)) ≪≫
        RootChangeColimitExamples.unitTree.{t}.endpointIso
          RootChangeColimitExamples.unitTree.{t}.lowerData)

/-- None of the actual mapped pieces is relatively compact under Nat at aleph0. -/
theorem originalMappedEmptyPieceNotPresentable
    (B : Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0}) :
    ¬ IsCardinalPresentable
      ((Under.map RootChangeColimitExamples.originalRoot).obj
        (RootChangeColimitExamples.unitTree.{t}.lowerData.obj B.1)) Cardinal.aleph0.{0} := by
  intro h
  let : IsCardinalPresentable
      ((Under.map RootChangeColimitExamples.originalRoot).obj
        (RootChangeColimitExamples.unitTree.{t}.lowerData.obj B.1)) Cardinal.aleph0.{0} := h
  exact RootChangeColimitExamples.originalMappedInitialNotPresentable.{t}
    (isCardinalPresentable_of_iso (originalMappedEmptyPieceIso.{t} B) Cardinal.aleph0.{0})

/-- Relative source compactness gives the actual factor despite BOTH failed absolute
source compactness and mapped-piece compactness. Both original equations remain. -/
theorem originalInfiniteCoefficientCapture :
    ∃ (B : Carrier (P := GoodCellTreeDataExamples.NoVertices) Cardinal.aleph0.{0}),
      BoundedLowerSupport.empty Cardinal.aleph0.{0} ≤ B ∧
        ∃ (p : GoodCellTreeDataExamples.quotientTree.{t}.endpointObj.right ⟶
          (RootChangeColimitExamples.unitTree.{t}.lowerData.obj B.1).right),
          GoodCellTreeDataExamples.quotientTree.{t}.hom ≫ p =
              RootChangeColimitExamples.originalRoot ≫
                (RootChangeColimitExamples.unitTree.{t}.lowerData.obj B.1).hom ∧
            p ≫ (RootChangeColimitExamples.unitTree.{t}.lowerData.map (le_top : B.1 ≤ ⊤) ≫
              (RootChangeColimitExamples.unitTree.{t}.endpointIso
                RootChangeColimitExamples.unitTree.{t}.lowerData).hom).right =
                  originalQuotientToUnit.{t} ∧
              ¬ IsCardinalPresentable
                ((Under.map RootChangeColimitExamples.originalRoot).obj
                  (RootChangeColimitExamples.unitTree.{t}.lowerData.obj B.1)) Cardinal.aleph0.{0} := by
  let : IsCardinalPresentable GoodCellTreeDataExamples.quotientTree.{t}.endpointObj
      Cardinal.aleph0.{0} := originalSourcePresentable.{t}
  obtain ⟨B, hSeed, p, hRoot, hEnd⟩ := existsTreeFactorContaining Cardinal.aleph0.{0}
    RootChangeColimitExamples.originalRoot RootChangeColimitExamples.unitTree.{t}
    RootChangeColimitExamples.unitTree_good.{t} RootChangeColimitExamples.unitTree.{t}.lowerData
    originalQuotientToUnit.{t} originalQuotientToUnit_root.{t}
    (BoundedLowerSupport.empty Cardinal.aleph0.{0})
  exact ⟨B, hSeed, p, hRoot, hEnd, originalMappedEmptyPieceNotPresentable.{t} B⟩

/-- The original full target tree, with all independent original attaching labels. -/
abbrev targetTree := BoundedLowerPresentationExamples.tree.{t}

/-- Its actual original endpoint right object is the given PUnit endpoint. -/
theorem target_endpoint_right : targetTree.{t}.endpointObj.right = PUnit.{1} := rfl

/-- Two actual different source roots in the same finite original family. -/
def familyRoots : Bool → Type
  | true => ℕ
  | false => PUnit.{1}

/-- Each original root arrow lands in the SAME original target Nat root. -/
def familyRho : ∀ b, familyRoots b ⟶ ℕ
  | true => 𝟙 ℕ
  | false => ↾fun _ => 0

/-- The family keeps the original one-fold source and actual initial PUnit source. -/
def familySources : ∀ b, Under (familyRoots b)
  | true => GoodCellTreeDataExamples.quotientTree.{t}.endpointObj
  | false => RootChangeColimitExamples.unitTree.{t}.endpointObj

instance familySourcesPresentable (b : Bool) :
    IsCardinalPresentable (familySources.{t} b) Cardinal.aleph0.{0} := by
  cases b with
  | false => exact RootChangeColimitExamples.originalInitialPresentable.{t}
  | true => exact originalSourcePresentable.{t}

/-- Each original raw family map retains its actual source right type. -/
def familyRaw : ∀ b, (familySources.{t} b).right ⟶ targetTree.{t}.endpointObj.right
  | true => ↾fun _ => PUnit.unit
  | false => 𝟙 PUnit.{1}

theorem familyRaw_root (b : Bool) :
    (familySources.{t} b).hom ≫ familyRaw.{t} b = familyRho b ≫ targetTree.{t}.hom := by
  cases b <;> ext n <;> rfl

/-- Each family member keeps a different actual original principal support seed. -/
def familySeeds (b : Bool) :
    Carrier (P := BoundedLowerPresentationExamples.Index) Cardinal.aleph0.{0} :=
  principal Cardinal.aleph0.{0} BoundedLowerPresentationExamples.good.{t}.predecessor_lt
    ⟨if b then 0 else 3⟩

/-- The same target tree returns one actual bounded support with both root and endpoint
equations for different original source roots, including every original seed. -/
theorem originalDifferentRootFamilyCapture :
    ∃ (B : Carrier (P := BoundedLowerPresentationExamples.Index) Cardinal.aleph0.{0}),
      BoundedLowerSupport.empty Cardinal.aleph0.{0} ≤ B ∧
        (∀ b, familySeeds.{t} b ≤ B) ∧
          ∃ (p : ∀ b, (familySources.{t} b).right ⟶ (targetTree.{t}.lowerData.obj B.1).right),
            ∀ b, (familySources.{t} b).hom ≫ p b =
                familyRho b ≫ (targetTree.{t}.lowerData.obj B.1).hom ∧
              p b ≫ (targetTree.{t}.lowerData.map (le_top : B.1 ≤ ⊤) ≫
                (targetTree.{t}.endpointIso targetTree.{t}.lowerData).hom).right = familyRaw.{t} b :=
  existsTreeFactorFamily Cardinal.aleph0.{0} targetTree.{t}
    BoundedLowerPresentationExamples.good.{t} targetTree.{t}.lowerData
    (hasCardinalLT_of_finite Bool Cardinal.aleph0.{0} le_rfl)
    familyRoots familyRho familySources.{t} familyRaw.{t} familyRaw_root.{t}
    (BoundedLowerSupport.empty Cardinal.aleph0.{0}) familySeeds.{t}

/-- The original empty bounded support in the SAME infinite target tree. -/
abbrev emptyTargetSupport :
    Carrier (P := BoundedLowerPresentationExamples.Index) Cardinal.aleph0.{0} :=
  BoundedLowerSupport.empty Cardinal.aleph0.{0}

/-- Its actual original empty-lower Iso under Nat, retaining the chosen L object. -/
def emptyTargetIso : targetTree.{t}.lowerData.obj emptyTargetSupport.1 ≅ Under.mk (𝟙 ℕ) :=
  targetTree.{t}.emptyLowerIso targetTree.{t}.lowerData

/-- Distinct original raw generator maps into that SAME chosen empty piece. -/
def originalPoint (n : ℕ) : PUnit.{1} ⟶
    (targetTree.{t}.lowerData.obj emptyTargetSupport.1).right :=
  (↾fun _ => n) ≫ emptyTargetIso.{t}.inv.right

theorem originalPoint_mapback (n : ℕ) :
    originalPoint.{t} n ≫ emptyTargetIso.{t}.hom.right = (↾fun _ => n) := by
  simp only [originalPoint, Category.assoc, Under.inv_right_hom_right, Under.mk_right,
    Category.comp_id]

theorem originalPointsDifferent : originalPoint.{t} 0 ≠ originalPoint.{t} 1 := by
  intro he
  have h := congrArg (fun k : PUnit.{1} ⟶
    (targetTree.{t}.lowerData.obj emptyTargetSupport.1).right => k ≫ emptyTargetIso.{t}.hom.right) he
  rw [originalPoint_mapback, originalPoint_mapback] at h
  exact Nat.zero_ne_one (ConcreteCategory.congr_hom h PUnit.unit)

/-- The actual original free source under the same nonpresentable Nat root. -/
abbrev equalitySource : Under ℕ := (Under.costar ℕ).obj PUnit.{1}

instance equalitySourcePresentable : IsCardinalPresentable equalitySource Cardinal.aleph0.{0} :=
  UnderColimits.costarPresentable Cardinal.aleph0.{0} PUnit.{1}

/-- The original raw point map transposes through the SAME original costar adjunction. -/
def equalityMap (n : ℕ) : equalitySource ⟶ targetTree.{t}.lowerData.obj emptyTargetSupport.1 :=
  UnderColimits.transpose (originalPoint.{t} n)

theorem equalityMap_root (n : ℕ) :
    equalitySource.hom ≫ (equalityMap.{t} n).right =
      (𝟙 ℕ) ≫ (targetTree.{t}.lowerData.obj emptyTargetSupport.1).hom := by
  simpa only [Category.id_comp] using Under.w (equalityMap.{t} n)

/-- The original right maps are genuinely different before the eventual-equality comparison. -/
theorem equalityMapsDifferent : (equalityMap.{t} 0).right ≠ (equalityMap.{t} 1).right := by
  intro he
  have h := Under.UnderMorphism.ext he
  have hRaw := congrArg ((Under.costarAdjForget ℕ).homEquiv PUnit.{1}
    (targetTree.{t}.lowerData.obj emptyTargetSupport.1)) h
  have hRaw' : originalPoint.{t} 0 = originalPoint.{t} 1 := by
    simpa only [equalityMap, UnderColimits.transpose, Equiv.apply_symm_apply] using hRaw
  exact originalPointsDifferent.{t} hRaw'

/-- Their original endpoint composites are equal, with the exact original chosen endpoint Iso. -/
theorem equalityMaps_endpoint :
    (equalityMap.{t} 0).right ≫ (targetTree.{t}.lowerData.map
      (le_top : emptyTargetSupport.1 ≤ ⊤) ≫
        (targetTree.{t}.endpointIso targetTree.{t}.lowerData).hom).right =
      (equalityMap.{t} 1).right ≫ (targetTree.{t}.lowerData.map
        (le_top : emptyTargetSupport.1 ≤ ⊤) ≫
          (targetTree.{t}.endpointIso targetTree.{t}.lowerData).hom).right := by
  let : Subsingleton targetTree.{t}.endpointObj.right := by
    rw [target_endpoint_right]
    infer_instance
  ext x
  exact Subsingleton.elim _ _

/-- Genuine eventual equality supplies a larger actual support, both original root laws,
and equality of the original distinct right functions after the SAME comparison map. -/
theorem originalNonmonomorphicEqualityCapture :
    ∃ (D : Carrier (P := BoundedLowerPresentationExamples.Index) Cardinal.aleph0.{0}),
      familySeeds.{t} true ≤ D ∧ ∃ (hBD : emptyTargetSupport.1 ≤ D.1),
        equalitySource.hom ≫ ((equalityMap.{t} 0).right ≫
            (targetTree.{t}.lowerData.map hBD).right) =
              (𝟙 ℕ) ≫ (targetTree.{t}.lowerData.obj D.1).hom ∧
          equalitySource.hom ≫ ((equalityMap.{t} 1).right ≫
            (targetTree.{t}.lowerData.map hBD).right) =
              (𝟙 ℕ) ≫ (targetTree.{t}.lowerData.obj D.1).hom ∧
            (equalityMap.{t} 0).right ≫ (targetTree.{t}.lowerData.map hBD).right =
              (equalityMap.{t} 1).right ≫ (targetTree.{t}.lowerData.map hBD).right :=
  existsTreeEqualityContaining Cardinal.aleph0.{0} (𝟙 ℕ) targetTree.{t}
    BoundedLowerPresentationExamples.good.{t} targetTree.{t}.lowerData
    emptyTargetSupport (familySeeds.{t} true) (equalityMap.{t} 0).right (equalityMap.{t} 1).right
    (equalityMap_root.{t} 0) (equalityMap_root.{t} 1) equalityMaps_endpoint.{t}

/-- Two genuinely nontrivial original equality constraints retain both distinct
raw maps and all original seeds on one actual bounded support. -/
theorem originalEqualityFamilyCapture :
    ∃ (D : Carrier (P := BoundedLowerPresentationExamples.Index) Cardinal.aleph0.{0}),
      BoundedLowerSupport.empty Cardinal.aleph0.{0} ≤ D ∧
        (∀ b, familySeeds.{t} b ≤ D) ∧ ∃ (hBD : emptyTargetSupport.1 ≤ D.1),
          ∀ _b : Bool,
            equalitySource.hom ≫ ((equalityMap.{t} 0).right ≫
                (targetTree.{t}.lowerData.map hBD).right) =
                  (𝟙 ℕ) ≫ (targetTree.{t}.lowerData.obj D.1).hom ∧
              equalitySource.hom ≫ ((equalityMap.{t} 1).right ≫
                (targetTree.{t}.lowerData.map hBD).right) =
                  (𝟙 ℕ) ≫ (targetTree.{t}.lowerData.obj D.1).hom ∧
                (equalityMap.{t} 0).right ≫ (targetTree.{t}.lowerData.map hBD).right =
                  (equalityMap.{t} 1).right ≫ (targetTree.{t}.lowerData.map hBD).right :=
  existsTreeEqualityFamily Cardinal.aleph0.{0} targetTree.{t}
    BoundedLowerPresentationExamples.good.{t} targetTree.{t}.lowerData
    (hasCardinalLT_of_finite Bool Cardinal.aleph0.{0} le_rfl)
    (fun _ => ℕ) (fun _ => 𝟙 ℕ) (fun _ => equalitySource)
    emptyTargetSupport (BoundedLowerSupport.empty Cardinal.aleph0.{0}) familySeeds.{t}
    (fun _ => (equalityMap.{t} 0).right) (fun _ => (equalityMap.{t} 1).right)
    (fun _ => equalityMap_root.{t} 0) (fun _ => equalityMap_root.{t} 1)
    (fun _ => equalityMaps_endpoint.{t})

/-- The empty equality-family instance retains both the base support and its original seed. -/
theorem originalEmptyEqualityFamily
    (B seed : Carrier (P := BoundedLowerPresentationExamples.Index) Cardinal.aleph0.{0}) :
    ∃ (D : Carrier (P := BoundedLowerPresentationExamples.Index) Cardinal.aleph0.{0}),
      seed ≤ D ∧ ∃ (hBD : B.1 ≤ D.1),
        (targetTree.{t}.lowerData.obj B.1).hom ≫ (targetTree.{t}.lowerData.map hBD).right =
          (targetTree.{t}.lowerData.obj D.1).hom := by
  let roots : Empty → Type := fun e => nomatch e
  let rhos : ∀ e, roots e ⟶ ℕ := fun e => nomatch e
  let sources : ∀ e, Under (roots e) := fun e => nomatch e
  let : ∀ e, IsCardinalPresentable (sources e) Cardinal.aleph0.{0} := fun e => nomatch e
  let seeds : Empty → Carrier (P := BoundedLowerPresentationExamples.Index) Cardinal.aleph0.{0} :=
    fun e => nomatch e
  let maps : ∀ e, (sources e).right ⟶ (targetTree.{t}.lowerData.obj B.1).right :=
    fun e => nomatch e
  obtain ⟨D, hSeed, _, hBD, _⟩ := existsTreeEqualityFamily Cardinal.aleph0.{0} targetTree.{t}
    BoundedLowerPresentationExamples.good.{t} targetTree.{t}.lowerData
    (hasCardinalLT_of_finite Empty Cardinal.aleph0.{0} le_rfl)
    roots rhos sources B seed seeds maps maps (fun e => nomatch e) (fun e => nomatch e)
    (fun e => nomatch e)
  exact ⟨D, hSeed, hBD, Under.w (targetTree.{t}.lowerData.map hBD)⟩

end RootChangeCaptureExamples
