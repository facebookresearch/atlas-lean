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

public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyAdapter
public import MathlibExt.Algebra.Homology.GradedTensorTower
public import MathlibExt.Algebra.Homology.TripleTensor
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.CategoryTheory.GradedObject.Preadditive
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Canonical graded homology: native tensor, unit and coherence

The object and Hom universes of the coefficient category are independent.
The tensorator is the native graded descent of the actual identity-chain-map
cycle pairing, and the unit is the native single-unit homology comparison.
Actual finite colimits and their preservation by the two tensor functors
supply all coproduct/cokernel/epi uses. No coherence data is a caller input.

This common owner extracts only the demonstrated cycle/unit/associator blocks
from the frozen base14 and larger-world17 banks. No ring, Field, Free, Small,
abelian or closed hypothesis is imposed on this structural category API.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.GradedHomology

private theorem assoc_right_tail {V : Type u} [Category.{v} V] {A B C D E : V}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) :
    (f ≫ g ≫ h) ≫ k = f ≫ g ≫ h ≫ k := by
  simp only [Category.assoc]

private theorem assoc_right_tail4 {V : Type u} [Category.{v} V] {A B C D E F : V}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : D ⟶ E) (k : E ⟶ F) :
    (f ≫ g ≫ h ≫ i) ≫ k = f ≫ g ≫ h ≫ i ≫ k := by
  simp only [Category.assoc]

private theorem comp_congr_right_tail {V : Type u} [Category.{v} V]
    {A B C D D' E F : V} (p : A ⟶ B) (q : B ⟶ C)
    (f : C ⟶ D) (g : D ⟶ E) (f' : C ⟶ D') (g' : D' ⟶ E) (t : E ⟶ F)
    (h : f ≫ g = f' ≫ g') :
    p ≫ q ≫ f ≫ g ≫ t = p ≫ q ≫ f' ≫ g' ≫ t :=
  congrArg (fun z => p ≫ q ≫ z)
    ((Category.assoc f g t).symm.trans
      ((congrArg (fun z => z ≫ t) h).trans (Category.assoc f' g' t)))

private theorem comp_collapse_right_tail {V : Type u} [Category.{v} V]
    {A B C D E : V} (p : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D)
    (f' : B ⟶ D) (t : D ⟶ E) (h : f ≫ g = f') :
    p ≫ f ≫ g ≫ t = p ≫ f' ≫ t :=
  congrArg (fun z => p ≫ z)
    ((Category.assoc f g t).symm.trans (congrArg (fun z => z ≫ t) h))

variable {V : Type u} [Category.{v} V] [Preadditive V]
  [CategoryWithHomology V] [HasZeroObject V] [HasFiniteColimits V]
  [MonoidalCategory V] [MonoidalPreadditive V]
  [∀ X : V, PreservesFiniteColimits (tensorLeft X)]
  [∀ X : V, PreservesFiniteColimits (tensorRight X)]

local notation "MC" => V
local notation "Ch" => ChainComplex MC ℕ
local notation "Gr" => GradedObject ℕ MC

/-- Native homology in every original degree. -/
abbrev homologyFunctor : Ch ⥤ Gr := gradedHomologyFunctor MC (ComplexShape.down ℕ)

/-- The canonical bidegree map descended from the actual cycle pairing. -/
abbrev pair (K L : Ch) (p q : ℕ) :
    K.homology p ⊗ L.homology q ⟶ (K ⊗ L).homology (p + q) :=
  ChainGradedPairing.pairHomology (𝟙 (K ⊗ L))
    (ChainGradedPairing.homologyDescentData (𝟙 (K ⊗ L))) p q

/-- The native categorical canonical cycle tensorator in the coefficient category. -/
def tensorator (K L : Ch) :
    homologyFunctor.obj K ⊗ homologyFunctor.obj L ⟶ homologyFunctor.obj (K ⊗ L) :=
  fun n => GradedObject.Monoidal.tensorObjDesc fun p q h =>
    pair K L p q ≫ (homologyIsoOfEq (K ⊗ L) h).hom

@[reassoc (attr := simp)]
theorem ι_tensorator (K L : Ch) (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K) (homologyFunctor.obj L)
      p q n h ≫ tensorator K L n =
      pair K L p q ≫ (homologyIsoOfEq (K ⊗ L) h).hom :=
  GradedObject.Monoidal.ι_tensorObjDesc _ p q h

/-- Actual bidegree cycle pairings are natural under both original chain maps. -/
@[reassoc]
theorem pair_naturality {K L K' L' : Ch} (f : K ⟶ K') (g : L ⟶ L') (p q : ℕ) :
    (homologyMap f p ⊗ₘ homologyMap g q) ≫ pair K' L' p q =
      pair K L p q ≫ homologyMap (f ⊗ₘ g) (p + q) := by
  let P : ChainGradedPairing K L (K ⊗ L) := 𝟙 _
  let Q : ChainGradedPairing K' L' (K' ⊗ L') := 𝟙 _
  exact ChainGradedPairing.pairHomology_naturality
    P (ChainGradedPairing.homologyDescentData P)
    Q (ChainGradedPairing.homologyDescentData Q) f g (f ⊗ₘ g)
    (fun i j => (ChainGradedPairing.pair_naturality P Q f g (f ⊗ₘ g)
      (by simp only [P, Q, Category.id_comp, Category.comp_id]; rfl) i j).symm) p q

/-- The native categorical tensorator is natural in both complex variables. -/
@[reassoc]
theorem tensorator_naturality {K L K' L' : Ch} (f : K ⟶ K') (g : L ⟶ L') :
    (homologyFunctor.map f ⊗ₘ homologyFunctor.map g) ≫ tensorator K' L' =
      tensorator K L ≫ homologyFunctor.map (f ⊗ₘ g) := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  let i := GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K) (homologyFunctor.obj L) p q n h
  let i' := GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K') (homologyFunctor.obj L') p q n h
  let t := GradedObject.Monoidal.tensorHom (homologyFunctor.map f) (homologyFunctor.map g) n
  let b := homologyMap f p ⊗ₘ homologyMap g q
  have ht : i ≫ t = b ≫ i' :=
    GradedObject.Monoidal.ι_tensorHom (homologyFunctor.map f) (homologyFunctor.map g) p q n h
  have hi := ι_tensorator K L p q n h
  have hi' := ι_tensorator K' L' p q n h
  change i ≫ (t ≫ tensorator K' L' n) =
    i ≫ (tensorator K L n ≫ homologyMap (f ⊗ₘ g) n)
  calc
    _ = b ≫ (pair K' L' p q ≫ (homologyIsoOfEq (K' ⊗ L') h).hom) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ tensorator K' L' n) ht).trans
          ((Category.assoc _ _ _).trans (congrArg (fun z => b ≫ z) hi')))
    _ = pair K L p q ≫ (homologyIsoOfEq (K ⊗ L) h).hom ≫ homologyMap (f ⊗ₘ g) n := by
      rw [← Category.assoc, pair_naturality, Category.assoc, homologyIsoOfEq_hom_naturality]
    _ = _ := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ homologyMap (f ⊗ₘ g) n) hi.symm).trans
        (Category.assoc _ _ _))


/-- The native tensor-unit homology comparison in the coefficient category. -/
def unitIso : 𝟙_ Gr ≅ homologyFunctor.obj (𝟙_ Ch) :=
  GradedObject.isoMk _ _ fun n => by
    by_cases h : n = 0
    · subst n
      exact GradedObject.Monoidal.tensorUnit₀ ≪≫
        (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).symm
    · exact ((GradedObject.Monoidal.isInitialTensorUnitApply n h).isZero.isoZero) ≪≫
        (isZero_single_obj_homology (ComplexShape.down ℕ) 0 (𝟙_ MC) n h).isoZero.symm

/-- The canonical map from the graded unit into homology of the chain unit. -/
def unitMap : 𝟙_ Gr ⟶ homologyFunctor.obj (𝟙_ Ch) := unitIso.hom

@[simp]
theorem unitMap_zero : unitMap (V := V) 0 =
    (GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := MC)).hom ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv := by
  simp only [unitMap, unitIso, GradedObject.isoMk_hom, dif_pos rfl, Iso.trans_hom,
    Iso.symm_hom]
  rfl

instance unitMap_isIso : IsIso (unitMap (V := V)) := by
  unfold unitMap
  infer_instance

/-- The canonical tensor pairing of cycles in a specified total degree. -/
def cyclesPair (K L : Ch) (p q n : ℕ) (h : p + q = n) :
    K.cycles p ⊗ L.cycles q ⟶ ((K ⊗ L)).cycles n :=
  ChainGradedPairing.pairCycles (𝟙 ((K ⊗ L)))
    (ChainGradedPairing.homologyDescentData (𝟙 ((K ⊗ L)))) p q ≫
      (cyclesIsoOfEq ((K ⊗ L)) h).hom

@[reassoc (attr := simp)]
theorem cyclesPair_i (K L : Ch) (p q n : ℕ) (h : p + q = n) :
    cyclesPair K L p q n h ≫ ((K ⊗ L)).iCycles n =
      (K.iCycles p ⊗ₘ L.iCycles q) ≫ ιTensorObj K L p q n h := by
  rw [cyclesPair, Category.assoc, cyclesIsoOfEq_hom_iCycles,
    ChainGradedPairing.pairCycles_i_assoc]
  simp only [ChainGradedPairing.pair, HomologicalComplex.id_f, Category.comp_id]
  have hId : ιTensorObj K L p q (p + q) rfl ≫ 𝟙 ((K ⊗ L).X (p + q)) =
      ιTensorObj K L p q (p + q) rfl := Category.comp_id _
  have hCast := ιTensorObj_comp_XIsoOfEq K L p q (p + q) n rfl h
  exact (congrArg (fun z => (K.iCycles p ⊗ₘ L.iCycles q) ≫ z ≫
    ((K ⊗ L).XIsoOfEq h).hom) hId).trans
      (congrArg (fun z => (K.iCycles p ⊗ₘ L.iCycles q) ≫ z) hCast)

@[reassoc (attr := simp)]
theorem quotient_tensorator (K L : Ch) (p q n : ℕ) (h : p + q = n) :
    (K.homologyπ p ⊗ₘ L.homologyπ q) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
        (homologyFunctor.obj L) p q n h ≫ tensorator K L n =
      cyclesPair K L p q n h ≫ ((K ⊗ L)).homologyπ n := by
  let Q := ChainGradedPairing.homologyDescentData (𝟙 ((K ⊗ L)))
  let c := ChainGradedPairing.pairCycles (𝟙 ((K ⊗ L))) Q p q
  have hi := ι_tensorator K L p q n h
  have hQ := ChainGradedPairing.tensor_homologyπ_comp_pairHomology
    (𝟙 ((K ⊗ L))) Q p q
  have hD := homologyπ_comp_homologyIsoOfEq_hom ((K ⊗ L)) h
  have hFirst := (congrArg (fun z => (K.homologyπ p ⊗ₘ L.homologyπ q) ≫ z) hi).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (homologyIsoOfEq ((K ⊗ L)) h).hom) hQ).trans
        ((Category.assoc _ _ _).trans (congrArg (fun z => c ≫ z) hD))))
  exact hFirst.trans (Category.assoc _ _ _).symm

omit [CategoryWithHomology V] [HasZeroObject V] [HasFiniteColimits V] [MonoidalPreadditive V] in
omit [Preadditive V] in
theorem tensor_epi {A A' B B' : MC} (f : A ⟶ A') (g : B ⟶ B')
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  letI : Epi ((tensorRight B).map f) :=
    CategoryTheory.preserves_epi_of_preservesColimit (tensorRight B) f
  letI : Epi ((tensorLeft A').map g) :=
    CategoryTheory.preserves_epi_of_preservesColimit (tensorLeft A') g
  rw [tensorHom_def]
  change Epi (((tensorRight B).map f) ≫ ((tensorLeft A').map g))
  infer_instance

omit [HasZeroObject V] [HasFiniteColimits V] [MonoidalPreadditive V] [∀ X : V, PreservesFiniteColimits (tensorLeft X)]
  [∀ X : V, PreservesFiniteColimits (tensorRight X)] in
omit [MonoidalCategory V] in
theorem cyclesDegreeTransport (K : Ch) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg (fun n => K.cycles n) h) ≫ K.iCycles j =
      K.iCycles i ≫ eqToHom (congrArg K.X h) := by
  cases h
  simp

omit [HasZeroObject V] [HasFiniteColimits V] [MonoidalPreadditive V] [∀ X : V, PreservesFiniteColimits (tensorLeft X)]
  [∀ X : V, PreservesFiniteColimits (tensorRight X)] in
omit [MonoidalCategory V] in
theorem homologyDegreeTransport (K : Ch) (i j : ℕ) (h : i = j) :
    K.homologyπ i ≫ eqToHom (congrArg (fun n => K.homology n) h) =
      eqToHom (congrArg (fun n => K.cycles n) h) ≫ K.homologyπ j := by
  cases h
  simp

/-- The actual bidegree pairing on cycle objects before homology descent. -/
abbrev cyclePair (K L : Ch) (p q : ℕ) :
    K.cycles p ⊗ L.cycles q ⟶ ((K ⊗ L)).cycles (p + q) :=
  ChainGradedPairing.pairCycles (𝟙 ((K ⊗ L)))
    (ChainGradedPairing.homologyDescentData (𝟙 ((K ⊗ L)))) p q

theorem cyclePair_i (K L : Ch) (p q : ℕ) :
    cyclePair K L p q ≫ ((K ⊗ L)).iCycles (p + q) =
      (K.iCycles p ⊗ₘ L.iCycles q) ≫ ιTensorObj K L p q (p + q) rfl := by
  exact (ChainGradedPairing.pairCycles_i (𝟙 ((K ⊗ L)))
    (ChainGradedPairing.homologyDescentData (𝟙 ((K ⊗ L)))) p q).trans (by
      change (K.iCycles p ⊗ₘ L.iCycles q) ≫
        (ιTensorObj K L p q (p + q) rfl ≫ 𝟙 ((K ⊗ L).X (p + q))) = _
      exact congrArg (fun z => (K.iCycles p ⊗ₘ L.iCycles q) ≫ z) (Category.comp_id _))

omit [CategoryWithHomology V] in
theorem termPair_assoc (A B C : Ch) (p q r : ℕ) :
    (ιTensorObj A B p q (p + q) rfl ⊗ₘ 𝟙 (C.X r)) ≫
      ιTensorObj ((A ⊗ B)) C (p + q) r ((p + q) + r) rfl ≫
      (α_ A B C).hom.f ((p + q) + r) ≫
      eqToHom (congrArg ((A ⊗ (B ⊗ C))).X (Nat.add_assoc p q r)) =
    (α_ (A.X p) (B.X q) (C.X r)).hom ≫
      (𝟙 (A.X p) ⊗ₘ ιTensorObj B C q r (q + r) rfl) ≫
      ιTensorObj A ((B ⊗ C)) p (q + r) (p + (q + r)) rfl := by
  let n := (p + q) + r
  let t := eqToHom (congrArg ((A ⊗ (B ⊗ C))).X (Nat.add_assoc p q r))
  have hL := ιTensorObj₃Left_eq A B C p q r n (p + q) rfl rfl
  have hR := ιTensorObj₃Right_eq A B C p q r n (q + r) rfl (Nat.add_assoc p q r).symm
  have hA := ιTensorObj₃Left_associator_hom A B C p q r n rfl
  have ht :
      ((ιTensorObj A B p q (p + q) rfl ▷ C.X r) ≫
        ιTensorObj ((A ⊗ B)) C (p + q) r n rfl) ≫ (α_ A B C).hom.f n =
      (α_ (A.X p) (B.X q) (C.X r)).hom ≫
        (A.X p ◁ ιTensorObj B C q r (q + r) rfl) ≫
          ιTensorObj A ((B ⊗ C)) p (q + r) n (Nat.add_assoc p q r).symm :=
    (congrArg (fun z => z ≫ (α_ A B C).hom.f n) hL.symm).trans
      (hA.trans (congrArg (fun z => (α_ (A.X p) (B.X q) (C.X r)).hom ≫ z) hR))
  have ht' := congrArg (fun z => z ≫ t) ht
  have hCast := ιTensorObj_comp_XIsoOfEq A ((B ⊗ C)) p (q + r) n
    (p + (q + r)) (Nat.add_assoc p q r).symm (Nat.add_assoc p q r)
  have hCast' : ιTensorObj A ((B ⊗ C)) p (q + r) n (Nat.add_assoc p q r).symm ≫ t =
      ιTensorObj A ((B ⊗ C)) p (q + r) (p + (q + r)) rfl := hCast
  have hFinal := (congrArg (fun z =>
    (α_ (A.X p) (B.X q) (C.X r)).hom ≫
      (A.X p ◁ ιTensorObj B C q r (q + r) rfl) ≫ z) hCast')
  have hCombined := ht'.trans (by simpa only [Category.assoc] using hFinal)
  simpa only [n, t, tensorHom_id, id_tensorHom, Category.assoc] using hCombined

theorem cyclePair_assoc (A B C : Ch) (p q r : ℕ) :
    (cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫
      cyclePair ((A ⊗ B)) C (p + q) r ≫
      cyclesMap (α_ A B C).hom ((p + q) + r) ≫
      eqToHom (congrArg (fun n => ((A ⊗ (B ⊗ C))).cycles n)
        (Nat.add_assoc p q r)) =
    (α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
      (𝟙 (A.cycles p) ⊗ₘ cyclePair B C q r) ≫
      cyclePair A ((B ⊗ C)) p (q + r) := by
  apply (cancel_mono (((A ⊗ (B ⊗ C))).iCycles (p + (q + r)))).1
  have hl : ((cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫
      cyclePair ((A ⊗ B)) C (p + q) r ≫
      cyclesMap (α_ A B C).hom ((p + q) + r) ≫
      eqToHom (congrArg (fun n => ((A ⊗ (B ⊗ C))).cycles n)
        (Nat.add_assoc p q r))) ≫ ((A ⊗ (B ⊗ C))).iCycles (p + (q + r)) =
      (((A.iCycles p ⊗ₘ B.iCycles q) ≫ ιTensorObj A B p q (p + q) rfl) ⊗ₘ
        C.iCycles r) ≫ ιTensorObj ((A ⊗ B)) C (p + q) r ((p + q) + r) rfl ≫
          (α_ A B C).hom.f ((p + q) + r) ≫
          eqToHom (congrArg ((A ⊗ (B ⊗ C))).X (Nat.add_assoc p q r)) := by
    simp only [Category.assoc]
    have hDegree := cyclesDegreeTransport ((A ⊗ (B ⊗ C)))
      ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
    rw [hDegree]
    have hMap := cyclesMap_i (α_ A B C).hom ((p + q) + r)
    have hMap' := congrArg (fun z =>
      (cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫ cyclePair ((A ⊗ B)) C (p + q) r ≫ z ≫
        eqToHom (congrArg ((A ⊗ (B ⊗ C))).X (Nat.add_assoc p q r))) hMap
    have hMap'' := hMap'
    simp only [Category.assoc] at hMap''
    refine hMap''.trans ?_
    have hOuter := cyclePair_i ((A ⊗ B)) C (p + q) r
    have hAB := cyclePair_i A B p q
    have hTensor : (cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫
        (((A ⊗ B)).iCycles (p + q) ⊗ₘ C.iCycles r) =
      ((cyclePair A B p q ≫ ((A ⊗ B)).iCycles (p + q)) ⊗ₘ C.iCycles r) :=
      (tensorHom_comp_tensorHom _ _ _ _).trans
        (congrArg (fun z => (cyclePair A B p q ≫ ((A ⊗ B)).iCycles (p + q)) ⊗ₘ z)
          (Category.id_comp _))
    calc
      _ = (cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫
          (((A ⊗ B)).iCycles (p + q) ⊗ₘ C.iCycles r) ≫
            ιTensorObj ((A ⊗ B)) C (p + q) r ((p + q) + r) rfl ≫
              (α_ A B C).hom.f ((p + q) + r) ≫
                eqToHom (congrArg ((A ⊗ (B ⊗ C))).X (Nat.add_assoc p q r)) := by
        simpa only [Category.assoc] using congrArg (fun z =>
          (cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫ z ≫
            (α_ A B C).hom.f ((p + q) + r) ≫
              eqToHom (congrArg ((A ⊗ (B ⊗ C))).X (Nat.add_assoc p q r))) hOuter
      _ = _ := by
        have hPair := hTensor.trans (congrArg (fun z => z ⊗ₘ C.iCycles r) hAB)
        simpa only [Category.assoc] using congrArg (fun z => z ≫
          ιTensorObj ((A ⊗ B)) C (p + q) r ((p + q) + r) rfl ≫
            (α_ A B C).hom.f ((p + q) + r) ≫
              eqToHom (congrArg ((A ⊗ (B ⊗ C))).X (Nat.add_assoc p q r))) hPair
  have hr : ((α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
      (𝟙 (A.cycles p) ⊗ₘ cyclePair B C q r) ≫
      cyclePair A ((B ⊗ C)) p (q + r)) ≫
      ((A ⊗ (B ⊗ C))).iCycles (p + (q + r)) =
      (α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
        (A.iCycles p ⊗ₘ ((B.iCycles q ⊗ₘ C.iCycles r) ≫
          ιTensorObj B C q r (q + r) rfl)) ≫
        ιTensorObj A ((B ⊗ C)) p (q + r) (p + (q + r)) rfl := by
    have hAC := cyclePair_i A ((B ⊗ C)) p (q + r)
    have hBC := cyclePair_i B C q r
    have hTensor : (𝟙 (A.cycles p) ⊗ₘ cyclePair B C q r) ≫
        (A.iCycles p ⊗ₘ ((B ⊗ C)).iCycles (q + r)) =
      A.iCycles p ⊗ₘ (cyclePair B C q r ≫ ((B ⊗ C)).iCycles (q + r)) :=
      (tensorHom_comp_tensorHom _ _ _ _).trans
        (congrArg (fun z => z ⊗ₘ
          (cyclePair B C q r ≫ ((B ⊗ C)).iCycles (q + r))) (Category.id_comp _))
    have hOuter := congrArg (fun z =>
      (α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
        (𝟙 (A.cycles p) ⊗ₘ cyclePair B C q r) ≫ z) hAC
    have hPair := hTensor.trans (congrArg (fun z => A.iCycles p ⊗ₘ z) hBC)
    have hOuter' := hOuter
    simpa only [Category.assoc] using hOuter'.trans
      (by simpa only [Category.assoc] using congrArg (fun z =>
        (α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫ z ≫
          ιTensorObj A ((B ⊗ C)) p (q + r) (p + (q + r)) rfl) hPair)
  have htL : (((A.iCycles p ⊗ₘ B.iCycles q) ≫ ιTensorObj A B p q (p + q) rfl) ⊗ₘ
      C.iCycles r) = ((A.iCycles p ⊗ₘ B.iCycles q) ⊗ₘ C.iCycles r) ≫
      (ιTensorObj A B p q (p + q) rfl ⊗ₘ 𝟙 (C.X r)) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have htR : (A.iCycles p ⊗ₘ ((B.iCycles q ⊗ₘ C.iCycles r) ≫
      ιTensorObj B C q r (q + r) rfl)) =
      (A.iCycles p ⊗ₘ (B.iCycles q ⊗ₘ C.iCycles r)) ≫
        (𝟙 (A.X p) ⊗ₘ ιTensorObj B C q r (q + r) rfl) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [hl, hr, htL, htR]
  simp only [Category.assoc]
  rw [termPair_assoc]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ (𝟙 (A.X p) ⊗ₘ ιTensorObj B C q r (q + r) rfl) ≫
      ιTensorObj A ((B ⊗ C)) p (q + r) (p + (q + r)) rfl)
    (associator_naturality (A.iCycles p) (B.iCycles q) (C.iCycles r))

/-- Associativity of the actual bidegree Künneth pairings, including the
literal equality-induced map between the two parenthesized total degrees. -/
theorem pair_assoc (A B C : Ch) (p q r : ℕ) :
    (pair A B p q ⊗ₘ 𝟙 (C.homology r)) ≫
      pair ((A ⊗ B)) C (p + q) r ≫
      homologyMap (α_ A B C).hom ((p + q) + r) ≫
      eqToHom (congrArg (fun n => ((A ⊗ (B ⊗ C))).homology n)
        (Nat.add_assoc p q r)) =
    (α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
      (𝟙 (A.homology p) ⊗ₘ pair B C q r) ≫ pair A ((B ⊗ C)) p (q + r) := by
  let a := A.homologyπ p
  let b := B.homologyπ q
  let c := C.homologyπ r
  let e := (a ⊗ₘ b) ⊗ₘ c
  letI : Epi (a ⊗ₘ b) := tensor_epi a b
  letI : Epi e := tensor_epi (a ⊗ₘ b) c
  apply (cancel_epi e).1
  have hl : e ≫ (pair A B p q ⊗ₘ 𝟙 (C.homology r)) =
      (cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫
        (((A ⊗ B)).homologyπ (p + q) ⊗ₘ c) := by
    dsimp only [e, a, b]
    rw [tensorHom_comp_tensorHom, ChainGradedPairing.tensor_homologyπ_comp_pairHomology,
      Category.comp_id, tensorHom_comp_tensorHom, Category.id_comp]
  have hr : (a ⊗ₘ (b ⊗ₘ c)) ≫ (𝟙 (A.homology p) ⊗ₘ pair B C q r) =
      (𝟙 (A.cycles p) ⊗ₘ cyclePair B C q r) ≫
        (a ⊗ₘ ((B ⊗ C)).homologyπ (q + r)) := by
    dsimp only [a, b, c]
    rw [tensorHom_comp_tensorHom, ChainGradedPairing.tensor_homologyπ_comp_pairHomology,
      Category.comp_id, tensorHom_comp_tensorHom, Category.id_comp]
  have hL : e ≫ ((pair A B p q ⊗ₘ 𝟙 (C.homology r)) ≫
      pair ((A ⊗ B)) C (p + q) r ≫
      homologyMap (α_ A B C).hom ((p + q) + r) ≫
      eqToHom (congrArg (fun n => ((A ⊗ (B ⊗ C))).homology n)
        (Nat.add_assoc p q r))) =
      (cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫
        cyclePair ((A ⊗ B)) C (p + q) r ≫
        cyclesMap (α_ A B C).hom ((p + q) + r) ≫
        eqToHom (congrArg (fun n => ((A ⊗ (B ⊗ C))).cycles n)
          (Nat.add_assoc p q r)) ≫ ((A ⊗ (B ⊗ C))).homologyπ (p + (q + r)) := by
    rw [← Category.assoc e, hl]
    simp only [Category.assoc]
    rw [ChainGradedPairing.tensor_homologyπ_comp_pairHomology_assoc]
    have hπ := homologyπ_naturality (α_ A B C).hom ((p + q) + r)
    have hπ' := congrArg (fun z => (cyclePair A B p q ⊗ₘ 𝟙 (C.cycles r)) ≫
      cyclePair ((A ⊗ B)) C (p + q) r ≫ z ≫
        eqToHom (congrArg (fun n => ((A ⊗ (B ⊗ C))).homology n)
          (Nat.add_assoc p q r))) hπ
    simp only [Category.assoc] at hπ'
    refine hπ'.trans ?_
    have hDegree := homologyDegreeTransport ((A ⊗ (B ⊗ C)))
      ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
    rw [hDegree]
  have hR : e ≫ ((α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
      (𝟙 (A.homology p) ⊗ₘ pair B C q r) ≫ pair A ((B ⊗ C)) p (q + r)) =
      (α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
        (𝟙 (A.cycles p) ⊗ₘ cyclePair B C q r) ≫
        cyclePair A ((B ⊗ C)) p (q + r) ≫
        ((A ⊗ (B ⊗ C))).homologyπ (p + (q + r)) := by
    dsimp only [e]
    rw [← Category.assoc, associator_naturality]
    simp only [Category.assoc]
    rw [← Category.assoc (a ⊗ₘ (b ⊗ₘ c)), hr]
    simp only [Category.assoc]
    rw [ChainGradedPairing.tensor_homologyπ_comp_pairHomology]
  rw [hL, hR]
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ ((A ⊗ (B ⊗ C))).homologyπ (p + (q + r)))
      (cyclePair_assoc A B C p q r)

@[reassoc]
theorem tripleTensorator_left (A B C : Ch) (p q r : ℕ) :
    GradedObject.Monoidal.ιTensorObj₃' (homologyFunctor.obj A) (homologyFunctor.obj B)
      (homologyFunctor.obj C) p q r ((p + q) + r) rfl ≫
      (tensorator A B ▷ homologyFunctor.obj C) ((p + q) + r) ≫
      tensorator (A ⊗ B) C ((p + q) + r) =
      (pair A B p q ⊗ₘ 𝟙 (C.homology r)) ≫ pair (A ⊗ B) C (p + q) r := by
  let X := homologyFunctor.obj A
  let Y := homologyFunctor.obj B
  let Z := homologyFunctor.obj C
  let W := homologyFunctor.obj (A ⊗ B)
  let n := (p + q) + r
  let i := GradedObject.Monoidal.ιTensorObj X Y p q (p + q) rfl
  let j := GradedObject.Monoidal.ιTensorObj (GradedObject.Monoidal.tensorObj X Y) Z (p + q) r n rfl
  let j' := GradedObject.Monoidal.ιTensorObj W Z (p + q) r n rfl
  let mu := tensorator A B
  let nu := tensorator (A ⊗ B) C
  have hMap : j ≫ (mu ▷ Z) n = (mu (p + q) ⊗ₘ 𝟙 (Z r)) ≫ j' :=
    GradedObject.Monoidal.ι_tensorHom mu (𝟙 Z) (p + q) r n rfl
  have hInner : i ≫ mu (p + q) = pair A B p q := by
    have h := ι_tensorator A B p q (p + q) rfl
    simpa only [homologyIsoOfEq_refl, Iso.refl_hom, Category.comp_id] using h
  have hOuter : j' ≫ nu n = pair (A ⊗ B) C (p + q) r := by
    have h := ι_tensorator (A ⊗ B) C (p + q) r n rfl
    simpa only [homologyIsoOfEq_refl, Iso.refl_hom, Category.comp_id] using h
  change ((i ▷ Z r) ≫ j) ≫ (mu ▷ Z) n ≫ nu n = _
  calc
    _ = (i ▷ Z r) ≫ (mu (p + q) ⊗ₘ 𝟙 (Z r)) ≫ j' ≫ nu n := by
      simpa only [Category.assoc] using
        congrArg (fun z => (i ▷ Z r) ≫ z ≫ nu n) hMap
    _ = ((i ≫ mu (p + q)) ⊗ₘ 𝟙 (Z r)) ≫ (j' ≫ nu n) := by
      rw [← tensorHom_id, ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
        Category.assoc]
    _ = _ := congrArg₂ (fun f g => (f ⊗ₘ 𝟙 (Z r)) ≫ g) hInner hOuter

@[reassoc]
theorem tripleTensorator_right (A B C : Ch) (p q r : ℕ) :
    GradedObject.Monoidal.ιTensorObj₃' (homologyFunctor.obj A) (homologyFunctor.obj B)
      (homologyFunctor.obj C) p q r ((p + q) + r) rfl ≫
      (α_ (homologyFunctor.obj A) (homologyFunctor.obj B) (homologyFunctor.obj C)).hom
        ((p + q) + r) ≫ (homologyFunctor.obj A ◁ tensorator B C) ((p + q) + r) ≫
      tensorator A (B ⊗ C) ((p + q) + r) =
      (α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
        (𝟙 (A.homology p) ⊗ₘ pair B C q r) ≫ pair A (B ⊗ C) p (q + r) ≫
        (homologyIsoOfEq (A ⊗ (B ⊗ C)) (Nat.add_assoc p q r).symm).hom := by
  let X := homologyFunctor.obj A
  let Y := homologyFunctor.obj B
  let Z := homologyFunctor.obj C
  let W := homologyFunctor.obj (B ⊗ C)
  let n := (p + q) + r
  let hN : p + (q + r) = n := (Nat.add_assoc p q r).symm
  let i := GradedObject.Monoidal.ιTensorObj Y Z q r (q + r) rfl
  let j := GradedObject.Monoidal.ιTensorObj X (GradedObject.Monoidal.tensorObj Y Z) p (q + r) n hN
  let j' := GradedObject.Monoidal.ιTensorObj X W p (q + r) n hN
  let mu := tensorator B C
  let nu := tensorator A (B ⊗ C)
  have hAssoc : GradedObject.Monoidal.ιTensorObj₃' X Y Z p q r n rfl ≫
      (α_ X Y Z).hom n = (α_ (X p) (Y q) (Z r)).hom ≫ (X p ◁ i) ≫ j := by
    exact GradedObject.Monoidal.ιTensorObj₃'_associator_hom X Y Z p q r n rfl
  have hMap : j ≫ (X ◁ mu) n = (𝟙 (X p) ⊗ₘ mu (q + r)) ≫ j' :=
    GradedObject.Monoidal.ι_tensorHom (𝟙 X) mu p (q + r) n hN
  have hInner : i ≫ mu (q + r) = pair B C q r := by
    simpa only [homologyIsoOfEq_refl, Iso.refl_hom, Category.comp_id] using
      ι_tensorator B C q r (q + r) rfl
  have hOuter : j' ≫ nu n = pair A (B ⊗ C) p (q + r) ≫
      (homologyIsoOfEq (A ⊗ (B ⊗ C)) hN).hom :=
    ι_tensorator A (B ⊗ C) p (q + r) n hN
  calc
    _ = (α_ (X p) (Y q) (Z r)).hom ≫ (X p ◁ i) ≫ j ≫ (X ◁ mu) n ≫ nu n := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ (X ◁ mu) n ≫ nu n) hAssoc
    _ = (α_ (X p) (Y q) (Z r)).hom ≫ (X p ◁ i) ≫
        (𝟙 (X p) ⊗ₘ mu (q + r)) ≫ j' ≫ nu n := by
      simpa only [Category.assoc] using congrArg (fun z =>
        (α_ (X p) (Y q) (Z r)).hom ≫ (X p ◁ i) ≫ z ≫ nu n) hMap
    _ = (α_ (X p) (Y q) (Z r)).hom ≫
        (𝟙 (X p) ⊗ₘ (i ≫ mu (q + r))) ≫ (j' ≫ nu n) := by
      have hTensor : (X p ◁ i) ≫ (𝟙 (X p) ⊗ₘ mu (q + r)) =
          𝟙 (X p) ⊗ₘ (i ≫ mu (q + r)) := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
      simpa only [Category.assoc] using congrArg (fun z =>
        (α_ (X p) (Y q) (Z r)).hom ≫ z ≫ j' ≫ nu n) hTensor
    _ = _ := congrArg₂ (fun f g => (α_ (X p) (Y q) (Z r)).hom ≫
      (𝟙 (X p) ⊗ₘ f) ≫ g) hInner hOuter

/-- Associator coherence for the canonical graded Künneth tensorator. -/
@[reassoc]
theorem tensorator_associativity (A B C : Ch) :
    tensorator A B ▷ homologyFunctor.obj C ≫ tensorator (A ⊗ B) C ≫
      homologyFunctor.map (α_ A B C).hom =
    (α_ (homologyFunctor.obj A) (homologyFunctor.obj B) (homologyFunctor.obj C)).hom ≫
      homologyFunctor.obj A ◁ tensorator B C ≫ tensorator A (B ⊗ C) := by
  funext n
  dsimp only [homologyFunctor, gradedHomologyFunctor]
  apply GradedObject.Monoidal.tensorObj₃'_ext
  intro p q r h
  subst n
  apply (cancel_mono (homologyIsoOfEq ((A ⊗ (B ⊗ C)))
    (Nat.add_assoc p q r)).hom).1
  let n := (p + q) + r
  let g := GradedObject.Monoidal.ιTensorObj₃' (homologyFunctor.obj A) (homologyFunctor.obj B)
    (homologyFunctor.obj C) p q r n rfl
  let u := (tensorator A B ▷ homologyFunctor.obj C) n
  let v := tensorator (A ⊗ B) C n
  let w := homologyMap (α_ A B C).hom n
  let t := (homologyIsoOfEq (A ⊗ (B ⊗ C)) (Nat.add_assoc p q r)).hom
  let s := (homologyIsoOfEq (A ⊗ (B ⊗ C)) (Nat.add_assoc p q r).symm).hom
  let R := (α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
    (𝟙 (A.homology p) ⊗ₘ pair B C q r) ≫ pair A (B ⊗ C) p (q + r)
  have hL := tripleTensorator_left A B C p q r
  have hR := tripleTensorator_right A B C p q r
  have hP : (pair A B p q ⊗ₘ 𝟙 (C.homology r)) ≫ pair (A ⊗ B) C (p + q) r ≫ w ≫ t = R := by
    simpa only [w, t, R, n, homologyIsoOfEq_hom] using pair_assoc A B C p q r
  have hLeft : (g ≫ u ≫ v ≫ w) ≫ t = R :=
    (assoc_right_tail4 g u v w t).trans
      ((assoc_right_tail g u v (w ≫ t)).symm.trans
        ((congrArg (fun z => z ≫ w ≫ t) hL).trans
          ((Category.assoc (pair A B p q ⊗ₘ 𝟙 (C.homology r))
            (pair (A ⊗ B) C (p + q) r) (w ≫ t)).trans hP)))
  have hCancel : s ≫ t = 𝟙 ((A ⊗ (B ⊗ C)).homology (p + (q + r))) := by
    dsimp only [s, t]
    rw [homologyIsoOfEq_hom_trans]
    simp only [homologyIsoOfEq_refl, Iso.refl_hom]
  have hRight :
      (g ≫ (α_ (homologyFunctor.obj A) (homologyFunctor.obj B) (homologyFunctor.obj C)).hom n ≫
        (homologyFunctor.obj A ◁ tensorator B C) n ≫ tensorator A (B ⊗ C) n) ≫ t = R :=
    (congrArg (fun z => z ≫ t) hR).trans
      ((congrArg (fun z => z ≫ t)
        (assoc_right_tail (α_ (A.homology p) (B.homology q) (C.homology r)).hom
          (𝟙 (A.homology p) ⊗ₘ pair B C q r) (pair A (B ⊗ C) p (q + r)) s).symm).trans
        ((Category.assoc R s t).trans
        ((congrArg (fun z => R ≫ z) hCancel).trans (Category.comp_id R))))
  change (g ≫ u ≫ v ≫ w) ≫ t = _
  exact hLeft.trans hRight.symm

omit [CategoryWithHomology V] in
theorem unitLeftTerm (K : Ch) (n : ℕ) :
    ((singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ⊗ₘ 𝟙 (K.X n)) ≫
      ιTensorObj (𝟙_ Ch) K 0 n n (zero_add n) ≫ (λ_ K).hom.f n =
      (λ_ (K.X n)).hom := by
  let e := λ_ K
  let l := λ_ (K.X n)
  let v := ((singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ⊗ₘ 𝟙 (K.X n)) ≫
    ιTensorObj (𝟙_ Ch) K 0 n n (zero_add n)
  have hInv : e.inv.f n = l.inv ≫ v := by
    have h := HomologicalComplex.leftUnitor'_inv K n
    change (HomologicalComplex.leftUnitor' K).inv n = l.inv ≫ v
    exact h.trans (by simp only [v, l, tensorHom_id, Category.assoc]; rfl)
  have hRound : e.inv.f n ≫ e.hom.f n = 𝟙 (K.X n) :=
    HomologicalComplex.congr_hom e.inv_hom_id n
  have hV : v = l.hom ≫ e.inv.f n :=
    ((Category.id_comp v).symm.trans
      ((congrArg (fun z => z ≫ v) l.hom_inv_id).symm.trans
        ((Category.assoc _ _ _).trans (congrArg (fun z => l.hom ≫ z) hInv.symm))))
  have hResult := (congrArg (fun z => z ≫ e.hom.f n) hV).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => l.hom ≫ z) hRound).trans (Category.comp_id l.hom)))
  simpa only [v, e, l, Category.assoc] using hResult

omit [CategoryWithHomology V] in
theorem unitRightTerm (K : Ch) (n : ℕ) :
    (𝟙 (K.X n) ⊗ₘ (singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv) ≫
      ιTensorObj K (𝟙_ Ch) n 0 n (add_zero n) ≫ (ρ_ K).hom.f n =
      (ρ_ (K.X n)).hom := by
  let e := ρ_ K
  let l := ρ_ (K.X n)
  let v := (𝟙 (K.X n) ⊗ₘ (singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv) ≫
    ιTensorObj K (𝟙_ Ch) n 0 n (add_zero n)
  have hInv : e.inv.f n = l.inv ≫ v := by
    have h := HomologicalComplex.rightUnitor'_inv K n
    change (HomologicalComplex.rightUnitor' K).inv n = l.inv ≫ v
    exact h.trans (by simp only [v, l, id_tensorHom, Category.assoc]; rfl)
  have hRound : e.inv.f n ≫ e.hom.f n = 𝟙 (K.X n) :=
    HomologicalComplex.congr_hom e.inv_hom_id n
  have hV : v = l.hom ≫ e.inv.f n :=
    ((Category.id_comp v).symm.trans
      ((congrArg (fun z => z ≫ v) l.hom_inv_id).symm.trans
        ((Category.assoc _ _ _).trans (congrArg (fun z => l.hom ≫ z) hInv.symm))))
  have hResult := (congrArg (fun z => z ≫ e.hom.f n) hV).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => l.hom ≫ z) hRound).trans (Category.comp_id l.hom)))
  simpa only [v, e, l, Category.assoc] using hResult

theorem unitLeftCycles (K : Ch) (n : ℕ) :
    ((singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ⊗ₘ
      𝟙 (K.cycles n)) ≫ cyclesPair (𝟙_ Ch) K 0 n n (zero_add n) ≫
      cyclesMap (λ_ K).hom n = (λ_ (K.cycles n)).hom := by
  apply (cancel_mono (K.iCycles n)).1
  let s := (singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv
  let t := (singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv
  let p := cyclesPair (𝟙_ Ch) K 0 n n (zero_add n)
  let l := λ_ K
  have hMap := cyclesMap_i l.hom n
  have hPair := cyclesPair_i (𝟙_ Ch) K 0 n n (zero_add n)
  have hSelf : s ≫ (𝟙_ Ch).iCycles 0 = t :=
    singleObjCyclesSelfIso_inv_iCycles (ComplexShape.down ℕ) 0 (𝟙_ MC)
  have hTensor : (s ⊗ₘ 𝟙 (K.cycles n)) ≫ ((𝟙_ Ch).iCycles 0 ⊗ₘ K.iCycles n) =
      t ⊗ₘ K.iCycles n :=
    (tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) hSelf (Category.id_comp _))
  have hTermTensor : (𝟙 (𝟙_ MC) ⊗ₘ K.iCycles n) ≫ (t ⊗ₘ 𝟙 (K.X n)) =
      t ⊗ₘ K.iCycles n :=
    (tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) (Category.id_comp _) (Category.comp_id _))
  calc
    _ = (s ⊗ₘ 𝟙 (K.cycles n)) ≫ p ≫ (𝟙_ Ch ⊗ K).iCycles n ≫ l.hom.f n := by
      simpa only [Category.assoc] using
        congrArg (fun z => (s ⊗ₘ 𝟙 (K.cycles n)) ≫ p ≫ z) hMap
    _ = (s ⊗ₘ 𝟙 (K.cycles n)) ≫ ((𝟙_ Ch).iCycles 0 ⊗ₘ K.iCycles n) ≫
        ιTensorObj (𝟙_ Ch) K 0 n n (zero_add n) ≫ l.hom.f n := by
      simpa only [Category.assoc] using
        congrArg (fun z => (s ⊗ₘ 𝟙 (K.cycles n)) ≫ z ≫ l.hom.f n) hPair
    _ = (t ⊗ₘ K.iCycles n) ≫ ιTensorObj (𝟙_ Ch) K 0 n n (zero_add n) ≫ l.hom.f n := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫
        ιTensorObj (𝟙_ Ch) K 0 n n (zero_add n) ≫ l.hom.f n) hTensor
    _ = (𝟙 (𝟙_ MC) ⊗ₘ K.iCycles n) ≫ (λ_ (K.X n)).hom := by
      have h := unitLeftTerm K n
      exact (congrArg (fun z => z ≫ ιTensorObj (𝟙_ Ch) K 0 n n (zero_add n) ≫ l.hom.f n)
        hTermTensor.symm).trans
          (by simpa only [t, l, Category.assoc] using
            congrArg (fun z => (𝟙 (𝟙_ MC) ⊗ₘ K.iCycles n) ≫ z) h)
    _ = _ := (congrArg (fun z => z ≫ (λ_ (K.X n)).hom)
      (id_tensorHom (𝟙_ MC) (K.iCycles n))).trans (leftUnitor_naturality (K.iCycles n))

theorem unitRightCycles (K : Ch) (n : ℕ) :
    (𝟙 (K.cycles n) ⊗ₘ (singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv) ≫
      cyclesPair K (𝟙_ Ch) n 0 n (add_zero n) ≫
      cyclesMap (ρ_ K).hom n = (ρ_ (K.cycles n)).hom := by
  apply (cancel_mono (K.iCycles n)).1
  let s := (singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv
  let t := (singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv
  let p := cyclesPair K (𝟙_ Ch) n 0 n (add_zero n)
  let l := ρ_ K
  have hMap := cyclesMap_i l.hom n
  have hPair := cyclesPair_i K (𝟙_ Ch) n 0 n (add_zero n)
  have hSelf : s ≫ (𝟙_ Ch).iCycles 0 = t :=
    singleObjCyclesSelfIso_inv_iCycles (ComplexShape.down ℕ) 0 (𝟙_ MC)
  have hTensor : (𝟙 (K.cycles n) ⊗ₘ s) ≫ (K.iCycles n ⊗ₘ (𝟙_ Ch).iCycles 0) =
      K.iCycles n ⊗ₘ t :=
    (tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) (Category.id_comp _) hSelf)
  have hTermTensor : (K.iCycles n ⊗ₘ 𝟙 (𝟙_ MC)) ≫ (𝟙 (K.X n) ⊗ₘ t) =
      K.iCycles n ⊗ₘ t :=
    (tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) (Category.comp_id _) (Category.id_comp _))
  calc
    _ = (𝟙 (K.cycles n) ⊗ₘ s) ≫ p ≫ (K ⊗ 𝟙_ Ch).iCycles n ≫ l.hom.f n := by
      simpa only [Category.assoc] using
        congrArg (fun z => (𝟙 (K.cycles n) ⊗ₘ s) ≫ p ≫ z) hMap
    _ = (𝟙 (K.cycles n) ⊗ₘ s) ≫ (K.iCycles n ⊗ₘ (𝟙_ Ch).iCycles 0) ≫
        ιTensorObj K (𝟙_ Ch) n 0 n (add_zero n) ≫ l.hom.f n := by
      simpa only [Category.assoc] using
        congrArg (fun z => (𝟙 (K.cycles n) ⊗ₘ s) ≫ z ≫ l.hom.f n) hPair
    _ = (K.iCycles n ⊗ₘ t) ≫ ιTensorObj K (𝟙_ Ch) n 0 n (add_zero n) ≫ l.hom.f n := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫
        ιTensorObj K (𝟙_ Ch) n 0 n (add_zero n) ≫ l.hom.f n) hTensor
    _ = (K.iCycles n ⊗ₘ 𝟙 (𝟙_ MC)) ≫ (ρ_ (K.X n)).hom := by
      have h := unitRightTerm K n
      exact (congrArg (fun z => z ≫ ιTensorObj K (𝟙_ Ch) n 0 n (add_zero n) ≫ l.hom.f n)
        hTermTensor.symm).trans
          (by simpa only [t, l, Category.assoc] using
            congrArg (fun z => (K.iCycles n ⊗ₘ 𝟙 (𝟙_ MC)) ≫ z) h)
    _ = _ := (congrArg (fun z => z ≫ (ρ_ (K.X n)).hom)
      (tensorHom_id (K.iCycles n) (𝟙_ MC))).trans (rightUnitor_naturality (K.iCycles n))

theorem unitHomologyInverseCycles :
    (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv =
      (singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ≫ (𝟙_ Ch).homologyπ 0 := by
  let eC := singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)
  let eH := singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)
  have h := singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv
    (ComplexShape.down ℕ) 0 (𝟙_ MC)
  exact ((congrArg (fun z => eC.inv ≫ z) h.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ eH.inv) eC.inv_hom_id).trans
        (Category.id_comp eH.inv)))).symm

/-- The native tensor unit paired with a homology class gives its left unitor. -/
theorem unit_left_pair (K : Ch) (n : ℕ) :
    ((singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ⊗ₘ
      𝟙 (K.homology n)) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj (𝟙_ Ch))
        (homologyFunctor.obj K) 0 n n (zero_add n) ≫ tensorator (𝟙_ Ch) K n ≫
      homologyMap (λ_ K).hom n = (λ_ (K.homology n)).hom := by
  dsimp only [homologyFunctor, gradedHomologyFunctor]
  let e := 𝟙 (𝟙_ MC) ⊗ₘ K.homologyπ n
  letI : Epi e := tensor_epi (𝟙 (𝟙_ MC)) (K.homologyπ n)
  apply (cancel_epi e).1
  have ht : e ≫ ((singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ⊗ₘ
      𝟙 (K.homology n)) =
      ((singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ⊗ₘ 𝟙 (K.cycles n)) ≫
        ((𝟙_ Ch).homologyπ 0 ⊗ₘ K.homologyπ n) := by
    dsimp only [e]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
    exact congrArg (fun f => f ⊗ₘ K.homologyπ n) (unitHomologyInverseCycles (V := V))
  let t := (singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ⊗ₘ 𝟙 (K.cycles n)
  let q := (𝟙_ Ch).homologyπ 0 ⊗ₘ K.homologyπ n
  let i := GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj (𝟙_ Ch))
    (homologyFunctor.obj K) 0 n n (zero_add n)
  let p := cyclesPair (𝟙_ Ch) K 0 n n (zero_add n)
  have hQ : q ≫ i ≫ tensorator (𝟙_ Ch) K n = p ≫ (𝟙_ Ch ⊗ K).homologyπ n :=
    quotient_tensorator (𝟙_ Ch) K 0 n n (zero_add n)
  have hMap := homologyπ_naturality (λ_ K).hom n
  have hCycles : t ≫ p ≫ cyclesMap (λ_ K).hom n = (λ_ (K.cycles n)).hom :=
    unitLeftCycles K n
  calc
    _ = t ≫ q ≫ i ≫ tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n := by
      exact (Category.assoc e ((singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv ⊗ₘ 𝟙 (K.homology n)) (i
        ≫ tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n)).symm.trans
        ((congrArg (fun z => z ≫ i ≫ tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n) ht).trans
          (Category.assoc t q (i ≫ tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n)))
    _ = t ≫ p ≫ (𝟙_ Ch ⊗ K).homologyπ n ≫ homologyMap (λ_ K).hom n := by
      exact (congrArg (fun z => t ≫ z) (assoc_right_tail q i (tensorator (𝟙_ Ch) K n) (homologyMap (λ_ K).hom
        n))).symm.trans
        ((congrArg (fun z => t ≫ z ≫ homologyMap (λ_ K).hom n) hQ).trans
          (congrArg (fun z => t ≫ z) (Category.assoc p _ (homologyMap (λ_ K).hom n))))
    _ = t ≫ p ≫ cyclesMap (λ_ K).hom n ≫ K.homologyπ n := by
      simpa only [Category.assoc] using congrArg (fun z => t ≫ p ≫ z) hMap
    _ = (λ_ (K.cycles n)).hom ≫ K.homologyπ n := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ K.homologyπ n) hCycles
    _ = _ := (leftUnitor_naturality (K.homologyπ n)).symm.trans
      (congrArg (fun z => z ≫ (λ_ (K.homology n)).hom)
        (id_tensorHom (𝟙_ MC) (K.homologyπ n)).symm)

/-- The native tensor unit paired on the right gives its right unitor. -/
theorem unit_right_pair (K : Ch) (n : ℕ) :
    (𝟙 (K.homology n) ⊗ₘ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv) ≫
      GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
        (homologyFunctor.obj (𝟙_ Ch)) n 0 n (add_zero n) ≫ tensorator K (𝟙_ Ch) n ≫
      homologyMap (ρ_ K).hom n = (ρ_ (K.homology n)).hom := by
  dsimp only [homologyFunctor, gradedHomologyFunctor]
  let e := K.homologyπ n ⊗ₘ 𝟙 (𝟙_ MC)
  letI : Epi e := tensor_epi (K.homologyπ n) (𝟙 (𝟙_ MC))
  apply (cancel_epi e).1
  have ht : e ≫ (𝟙 (K.homology n) ⊗ₘ
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv) =
      (𝟙 (K.cycles n) ⊗ₘ (singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv) ≫
        (K.homologyπ n ⊗ₘ (𝟙_ Ch).homologyπ 0) := by
    dsimp only [e]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
    exact congrArg (fun f => K.homologyπ n ⊗ₘ f) (unitHomologyInverseCycles (V := V))
  let t := 𝟙 (K.cycles n) ⊗ₘ (singleObjCyclesSelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv
  let q := K.homologyπ n ⊗ₘ (𝟙_ Ch).homologyπ 0
  let i := GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
    (homologyFunctor.obj (𝟙_ Ch)) n 0 n (add_zero n)
  let p := cyclesPair K (𝟙_ Ch) n 0 n (add_zero n)
  have hQ : q ≫ i ≫ tensorator K (𝟙_ Ch) n = p ≫ (K ⊗ 𝟙_ Ch).homologyπ n :=
    quotient_tensorator K (𝟙_ Ch) n 0 n (add_zero n)
  have hMap := homologyπ_naturality (ρ_ K).hom n
  have hCycles : t ≫ p ≫ cyclesMap (ρ_ K).hom n = (ρ_ (K.cycles n)).hom :=
    unitRightCycles K n
  calc
    _ = t ≫ q ≫ i ≫ tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n := by
      exact (Category.assoc e (𝟙 (K.homology n) ⊗ₘ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ MC)).inv) (i
        ≫ tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n)).symm.trans
        ((congrArg (fun z => z ≫ i ≫ tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n) ht).trans
          (Category.assoc t q (i ≫ tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n)))
    _ = t ≫ p ≫ (K ⊗ 𝟙_ Ch).homologyπ n ≫ homologyMap (ρ_ K).hom n := by
      exact (congrArg (fun z => t ≫ z) (assoc_right_tail q i (tensorator K (𝟙_ Ch) n) (homologyMap (ρ_ K).hom
        n))).symm.trans
        ((congrArg (fun z => t ≫ z ≫ homologyMap (ρ_ K).hom n) hQ).trans
          (congrArg (fun z => t ≫ z) (Category.assoc p _ (homologyMap (ρ_ K).hom n))))
    _ = t ≫ p ≫ cyclesMap (ρ_ K).hom n ≫ K.homologyπ n := by
      simpa only [Category.assoc] using congrArg (fun z => t ≫ p ≫ z) hMap
    _ = (ρ_ (K.cycles n)).hom ≫ K.homologyπ n := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ K.homologyπ n) hCycles
    _ = _ := (rightUnitor_naturality (K.homologyπ n)).symm.trans
      (congrArg (fun z => z ≫ (ρ_ (K.homology n)).hom)
        (tensorHom_id (K.homologyπ n) (𝟙_ MC)).symm)

/-- Left unit coherence for the canonical cycle Künneth tensorator. -/
theorem tensorator_left_unitality (K : Ch) :
    (λ_ (homologyFunctor.obj K)).hom = unitMap ▷ homologyFunctor.obj K ≫
      tensorator (𝟙_ Ch) K ≫ homologyFunctor.map (λ_ K).hom := by
  apply (cancel_epi (λ_ (homologyFunctor.obj K)).inv).1
  funext n
  dsimp only [homologyFunctor, gradedHomologyFunctor]
  rw [Iso.inv_hom_id]
  let X := homologyFunctor.obj K
  let u := GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := V)
  let j := GradedObject.Monoidal.ιTensorObj (𝟙_ Gr) X 0 n n (zero_add n)
  let i := GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj (𝟙_ Ch)) X 0 n n (zero_add n)
  let l := λ_ (K.homology n)
  let e := singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ V)
  have hInv : (λ_ X).inv n = l.inv ≫ (u.inv ▷ X n) ≫ j :=
    GradedObject.Monoidal.leftUnitor_inv_apply X n
  have hMap : j ≫ (unitMap ▷ X) n = (unitMap 0 ⊗ₘ 𝟙 (X n)) ≫ i :=
    GradedObject.Monoidal.ι_tensorHom unitMap (𝟙 X) 0 n n (zero_add n)
  have hUnit : u.inv ≫ unitMap 0 = e.inv :=
    (congrArg (fun z => u.inv ≫ z) (unitMap_zero (V := V))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ e.inv) u.inv_hom_id).trans (Category.id_comp _)))
  have hTensor : (u.inv ▷ X n) ≫ (unitMap 0 ⊗ₘ 𝟙 (X n)) = e.inv ⊗ₘ 𝟙 (X n) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => z ⊗ₘ 𝟙 (X n)) hUnit
  have hPair := unit_left_pair K n
  change 𝟙 (X n) = (λ_ X).inv n ≫ (unitMap ▷ X) n ≫
    tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n
  have hFirst := congrArg (fun z => z ≫ (unitMap ▷ X) n ≫
    tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n) hInv
  have hResult := hFirst.trans
    (assoc_right_tail l.inv (u.inv ▷ X n) j ((unitMap ▷ X) n ≫ tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n))
  have hResult := hResult.trans
    (comp_congr_right_tail l.inv (u.inv ▷ X n) j ((unitMap ▷ X) n) (unitMap 0 ⊗ₘ 𝟙 (X n)) i
      (tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n) hMap)
  have hResult := hResult.trans
    (comp_collapse_right_tail l.inv (u.inv ▷ X n) (unitMap 0 ⊗ₘ 𝟙 (X n)) (e.inv ⊗ₘ 𝟙 (X n))
      (i ≫ tensorator (𝟙_ Ch) K n ≫ homologyMap (λ_ K).hom n) hTensor)
  have hResult := hResult.trans (congrArg (fun z => l.inv ≫ z) hPair)
  exact (hResult.trans l.inv_hom_id).symm

/-- Right unit coherence for the canonical cycle Künneth tensorator. -/
theorem tensorator_right_unitality (K : Ch) :
    (ρ_ (homologyFunctor.obj K)).hom = homologyFunctor.obj K ◁ unitMap ≫
      tensorator K (𝟙_ Ch) ≫ homologyFunctor.map (ρ_ K).hom := by
  apply (cancel_epi (ρ_ (homologyFunctor.obj K)).inv).1
  funext n
  dsimp only [homologyFunctor, gradedHomologyFunctor]
  rw [Iso.inv_hom_id]
  let X := homologyFunctor.obj K
  let u := GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := V)
  let j := GradedObject.Monoidal.ιTensorObj X (𝟙_ Gr) n 0 n (add_zero n)
  let i := GradedObject.Monoidal.ιTensorObj X (homologyFunctor.obj (𝟙_ Ch)) n 0 n (add_zero n)
  let l := ρ_ (K.homology n)
  let e := singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ V)
  have hInv : (ρ_ X).inv n = l.inv ≫ (X n ◁ u.inv) ≫ j :=
    GradedObject.Monoidal.rightUnitor_inv_apply X n
  have hMap : j ≫ (X ◁ unitMap) n = (𝟙 (X n) ⊗ₘ unitMap 0) ≫ i :=
    GradedObject.Monoidal.ι_tensorHom (𝟙 X) unitMap n 0 n (add_zero n)
  have hUnit : u.inv ≫ unitMap 0 = e.inv :=
    (congrArg (fun z => u.inv ≫ z) (unitMap_zero (V := V))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ e.inv) u.inv_hom_id).trans (Category.id_comp _)))
  have hTensor : (X n ◁ u.inv) ≫ (𝟙 (X n) ⊗ₘ unitMap 0) = 𝟙 (X n) ⊗ₘ e.inv := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => 𝟙 (X n) ⊗ₘ z) hUnit
  have hPair := unit_right_pair K n
  change 𝟙 (X n) = (ρ_ X).inv n ≫ (X ◁ unitMap) n ≫
    tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n
  have hFirst := congrArg (fun z => z ≫ (X ◁ unitMap) n ≫
    tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n) hInv
  have hResult := hFirst.trans
    (assoc_right_tail l.inv (X n ◁ u.inv) j ((X ◁ unitMap) n ≫ tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n))
  have hResult := hResult.trans
    (comp_congr_right_tail l.inv (X n ◁ u.inv) j ((X ◁ unitMap) n) (𝟙 (X n) ⊗ₘ unitMap 0) i
      (tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n) hMap)
  have hResult := hResult.trans
    (comp_collapse_right_tail l.inv (X n ◁ u.inv) (𝟙 (X n) ⊗ₘ unitMap 0) (𝟙 (X n) ⊗ₘ e.inv)
      (i ≫ tensorator K (𝟙_ Ch) n ≫ homologyMap (ρ_ K).hom n) hTensor)
  have hResult := hResult.trans (congrArg (fun z => l.inv ≫ z) hPair)
  exact (hResult.trans l.inv_hom_id).symm

/-- The earned lax monoidal structure on native graded homology
for the structural coefficient category. -/
def laxMonoidal : (homologyFunctor (V := V)).LaxMonoidal where
  ε := unitMap
  μ := tensorator
  μ_natural_left f K := by
    have hId := (homologyFunctor (V := V)).map_id K
    have h := tensorator_naturality f (𝟙 K)
    rw [hId, tensorHom_id] at h
    simpa only [tensorHom_id] using h
  μ_natural_right K f := by
    have hId := (homologyFunctor (V := V)).map_id K
    have h := tensorator_naturality (𝟙 K) f
    rw [hId, id_tensorHom] at h
    simpa only [id_tensorHom] using h
  associativity := tensorator_associativity
  left_unitality := tensorator_left_unitality
  right_unitality := tensorator_right_unitality


end HomologicalComplex.GradedHomology
