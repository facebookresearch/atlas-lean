/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenGluing

/-!
# Original iterated finite S-construction categories

A list of stage degrees describes successive applications of the actual
S-construction. At every step the original zero diagram and successive
pushout-corner Waldhausen value supply the structures used by the next
step. No category, cofibration or weak-equivalence model is replaced.

The categorical iteration is a prerequisite for the multisimplicial
structure and genuine spectrum structure maps; these are subsequent proofs.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Waldhausen.SConstruction

section

universe w

private structure IteratedStageData where
  carrier : Type w
  category : Category.{v} carrier
  zero : @HasZeroObject carrier category
  waldhausen : @WaldhausenCategoryWithoutGluing carrier category zero

private def iteratedStageData (C : Type (max u v)) [Category.{v} C]
    [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] : List ℕ → IteratedStageData.{v, max u v}
  | [] => ⟨C, inferInstance, inferInstance, inferInstance⟩
  | n :: ns =>
      let D := iteratedStageData C ns
      letI : Category.{v} D.carrier := D.category
      letI : HasZeroObject D.carrier := D.zero
      letI : WaldhausenCategoryWithoutGluing D.carrier := D.waldhausen
      letI : HasZeroObject (Stage D.carrier n) := generalStageHasZeroObject D.carrier n
      ⟨Stage D.carrier n, inferInstance, generalStageHasZeroObject D.carrier n,
        generalStageWaldhausenCategory D.carrier n⟩

end

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Successive original S-stages indexed by their actual degree list. -/
@[no_expose]
def IteratedStage (ns : List ℕ) : Type (max u v) :=
  (iteratedStageData C ns).carrier

/-- The category is inherited from the original full S-stage category at each step. -/
@[no_expose]
instance iteratedStageCategory (ns : List ℕ) : Category.{v} (IteratedStage C ns) :=
  (iteratedStageData C ns).category

/-- Every iteration has its actual original canonical stage zero object. -/
instance iteratedStageHasZeroObject (ns : List ℕ) : HasZeroObject (IteratedStage C ns) :=
  (iteratedStageData C ns).zero

/-- Every iteration retains the original named successive-corner
cofibrations, weak maps and stage pushout constructor. -/
@[no_expose]
instance iteratedStageWaldhausenCategory (ns : List ℕ) :
    WaldhausenCategoryWithoutGluing (IteratedStage C ns) :=
  (iteratedStageData C ns).waldhausen

/-- The base gluing axiom propagates through every original finite S-iteration. -/
theorem iteratedStageWaldhausenGluingAxiom (hGlue : WaldhausenGluingAxiom (C := C)) :
    ∀ ns : List ℕ, WaldhausenGluingAxiom (C := IteratedStage C ns)
  | [] => by
      dsimp [IteratedStage, iteratedStageCategory, iteratedStageHasZeroObject,
        iteratedStageWaldhausenCategory, iteratedStageData]
      exact hGlue
  | n :: ns => by
      have hPrev := iteratedStageWaldhausenGluingAxiom hGlue ns
      have hStage := generalStageWaldhausenGluingAxiom (IteratedStage C ns) hPrev n
      dsimp [IteratedStage, iteratedStageCategory, iteratedStageHasZeroObject,
        iteratedStageWaldhausenCategory, iteratedStageData] at hStage ⊢
      exact hStage

/-- The zero-fold construction is exactly the original input category. -/
theorem iteratedStage_nil : IteratedStage C [] = C := by
  unfold IteratedStage iteratedStageData
  rfl

/-- The successor iteration is the original S-stage on the prior iteration. -/
theorem iteratedStage_cons (n : ℕ) (ns : List ℕ) :
    IteratedStage C (n :: ns) = Stage (IteratedStage C ns) n := by
  unfold IteratedStage iteratedStageData
  rfl

/-- The original zero-fold carrier and category give their canonical equivalence. -/
@[no_expose]
def iteratedStageNilEquivalence : IteratedStage C [] ≌ C := by
  dsimp [IteratedStage, iteratedStageCategory, iteratedStageData]
  exact Equivalence.refl

/-- The original forward and reverse Nil charts compose to the
literal identity on the same original zero-fold category. -/
theorem iteratedStageNilEquivalence_functor_inverse :
    (iteratedStageNilEquivalence C).functor ⋙ (iteratedStageNilEquivalence C).inverse =
      𝟭 (IteratedStage C []) := by
  unfold iteratedStageNilEquivalence
  rfl

/-- The reverse and forward Nil charts compose to the literal
identity on the original input category. -/
theorem iteratedStageNilEquivalence_inverse_functor :
    (iteratedStageNilEquivalence C).inverse ⋙ (iteratedStageNilEquivalence C).functor =
      𝟭 C := by
  unfold iteratedStageNilEquivalence
  rfl

/-- The original successor carrier and category give their canonical equivalence. -/
@[no_expose]
def iteratedStageConsEquivalence (n : ℕ) (ns : List ℕ) :
    IteratedStage C (n :: ns) ≌ Stage (IteratedStage C ns) n := by
  dsimp [IteratedStage, iteratedStageCategory, iteratedStageData]
  exact Equivalence.refl

/-- Both directions of the canonical successor equivalence preserve the
same original named zero and Waldhausen structures. -/
theorem iteratedStageConsEquivalence_exact (n : ℕ) (ns : List ℕ) :
    letI : HasZeroObject (Stage (IteratedStage C ns) n) :=
      generalStageHasZeroObject (IteratedStage C ns) n
    letI : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C ns) n) :=
      generalStageWaldhausenCategory (IteratedStage C ns) n
    (iteratedStageConsEquivalence C n ns).functor.IsWaldhausenExact ∧
      (iteratedStageConsEquivalence C n ns).inverse.IsWaldhausenExact := by
  let : HasZeroObject (Stage (IteratedStage C ns) n) :=
    generalStageHasZeroObject (IteratedStage C ns) n
  let : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C ns) n) :=
    generalStageWaldhausenCategory (IteratedStage C ns) n
  dsimp [iteratedStageConsEquivalence, IteratedStage, iteratedStageCategory,
    iteratedStageHasZeroObject, iteratedStageWaldhausenCategory, iteratedStageData,
    Equivalence.refl, id]
  exact ⟨Functor.IsWaldhausenExact.id (C := Stage (IteratedStage C ns) n),
    Functor.IsWaldhausenExact.id (C := Stage (IteratedStage C ns) n)⟩

/-- The successor transport retains the literal identity on the original carrier. -/
theorem iteratedStageConsEquivalence_functor_inverse (n : ℕ) (ns : List ℕ) :
    (iteratedStageConsEquivalence C n ns).functor ⋙
        (iteratedStageConsEquivalence C n ns).inverse = 𝟭 (IteratedStage C (n :: ns)) := by
  unfold iteratedStageConsEquivalence
  rfl

/-- The reverse successor transport is the literal identity on the original stage carrier. -/
theorem iteratedStageConsEquivalence_inverse_functor (n : ℕ) (ns : List ℕ) :
    (iteratedStageConsEquivalence C n ns).inverse ⋙
        (iteratedStageConsEquivalence C n ns).functor = 𝟭 (Stage (IteratedStage C ns) n) := by
  unfold iteratedStageConsEquivalence
  rfl

/-- The original base carrier equivalence preserves its actual chosen zero literally. -/
theorem iteratedStageNilEquivalence_obj_zero :
    (iteratedStageNilEquivalence C).functor.obj (0 : IteratedStage C []) = (0 : C) := by
  dsimp [iteratedStageNilEquivalence, IteratedStage, iteratedStageCategory,
    iteratedStageHasZeroObject, iteratedStageData, Equivalence.refl, id]
  rfl

/-- The original reverse Nil chart retains the same actual base zero. -/
theorem iteratedStageNilEquivalence_inverse_obj_zero :
    (iteratedStageNilEquivalence C).inverse.obj (0 : C) = (0 : IteratedStage C []) := by
  dsimp [iteratedStageNilEquivalence, IteratedStage, iteratedStageCategory,
    iteratedStageHasZeroObject, iteratedStageData, Equivalence.refl, id]
  rfl

/-- The original successor carrier's chosen zero is zero in the original stage category. -/
theorem iteratedStageConsEquivalence_obj_zero_isZero (n : ℕ) (ns : List ℕ) :
    IsZero ((iteratedStageConsEquivalence C n ns).functor.obj
      (0 : IteratedStage C (n :: ns))) := by
  dsimp [iteratedStageConsEquivalence, IteratedStage, iteratedStageCategory,
    iteratedStageHasZeroObject, iteratedStageData, Equivalence.refl, id]
  let : HasZeroObject (Stage (IteratedStage C ns) n) :=
    generalStageHasZeroObject (IteratedStage C ns) n
  exact isZero_zero (Stage (IteratedStage C ns) n)

/-- The original chosen zero is canonically isomorphic to the constructed constant-zero stage. -/
def iteratedStageConsEquivalenceObjZeroIso (n : ℕ) (ns : List ℕ) :
    (iteratedStageConsEquivalence C n ns).functor.obj (0 : IteratedStage C (n :: ns)) ≅
      generalStageZero (IteratedStage C ns) n :=
  (iteratedStageConsEquivalence_obj_zero_isZero C n ns).iso
    (generalStageZero_isZero (IteratedStage C ns) n)

/-- The inverse original carrier transport retains the constructed stage's zero property. -/
theorem iteratedStageConsEquivalence_inverse_zero_isZero (n : ℕ) (ns : List ℕ) :
    IsZero ((iteratedStageConsEquivalence C n ns).inverse.obj
      (generalStageZero (IteratedStage C ns) n)) := by
  dsimp [iteratedStageConsEquivalence, IteratedStage, iteratedStageCategory,
    iteratedStageData, Equivalence.refl, id]
  exact generalStageZero_isZero (IteratedStage C ns) n

/-- The inverse original carrier transport identifies its constructed zero with the chosen zero. -/
def iteratedStageConsEquivalenceInverseZeroIso (n : ℕ) (ns : List ℕ) :
    (iteratedStageConsEquivalence C n ns).inverse.obj
      (generalStageZero (IteratedStage C ns) n) ≅ (0 : IteratedStage C (n :: ns)) :=
  (iteratedStageConsEquivalence_inverse_zero_isZero C n ns).isoZero

/-- Both directions of the canonical base equivalence preserve the original
input Waldhausen structure. -/
theorem iteratedStageNilEquivalence_exact :
    (iteratedStageNilEquivalence C).functor.IsWaldhausenExact ∧
      (iteratedStageNilEquivalence C).inverse.IsWaldhausenExact := by
  dsimp [iteratedStageNilEquivalence, IteratedStage, iteratedStageCategory,
    iteratedStageHasZeroObject, iteratedStageWaldhausenCategory, iteratedStageData,
    Equivalence.refl, id]
  exact ⟨Functor.IsWaldhausenExact.id (C := C), Functor.IsWaldhausenExact.id (C := C)⟩

/-- Equal original degree lists give their literal canonical carrier equivalence. -/
def iteratedStageListEquivalence {ns ms : List ℕ} (h : ns = ms) :
    IteratedStage C ns ≌ IteratedStage C ms := by
  subst ms
  exact Equivalence.refl

/-- Equality transport retains the original zero and Waldhausen values. -/
theorem iteratedStageListEquivalence_exact {ns ms : List ℕ} (h : ns = ms) :
    (iteratedStageListEquivalence C h).functor.IsWaldhausenExact ∧
      (iteratedStageListEquivalence C h).inverse.IsWaldhausenExact := by
  subst ms
  dsimp [iteratedStageListEquivalence, Equivalence.refl]
  exact ⟨Functor.IsWaldhausenExact.id (C := IteratedStage C ns),
    Functor.IsWaldhausenExact.id (C := IteratedStage C ns)⟩

/-- Equal-list carrier transport retains the actual source identity. -/
theorem iteratedStageListEquivalence_functor_inverse {ns ms : List ℕ} (h : ns = ms) :
    (iteratedStageListEquivalence C h).functor ⋙ (iteratedStageListEquivalence C h).inverse =
      𝟭 (IteratedStage C ns) := by
  subst ms
  rfl

/-- Equal-list carrier transport retains the actual target identity. -/
theorem iteratedStageListEquivalence_inverse_functor {ns ms : List ℕ} (h : ns = ms) :
    (iteratedStageListEquivalence C h).inverse ⋙ (iteratedStageListEquivalence C h).functor =
      𝟭 (IteratedStage C ms) := by
  subst ms
  rfl

/-- The exact original successor carrier equivalence for a tuple degree list. -/
def iteratedStageOfFnSuccEquivalence {r : ℕ} (d : Fin (r + 1) → ℕ) :
    IteratedStage C (List.ofFn d) ≌
      Stage (IteratedStage C (List.ofFn (fun i => d i.succ))) (d 0) :=
  (iteratedStageListEquivalence C (List.ofFn_succ (f := d))).trans
    (iteratedStageConsEquivalence C _ _)

/-- Both directions of tuple-carrier transport retain the earned original
stage structures. -/
theorem iteratedStageOfFnSuccEquivalence_exact {r : ℕ} (d : Fin (r + 1) → ℕ) :
    letI : HasZeroObject (Stage (IteratedStage C (List.ofFn (fun i => d i.succ))) (d 0)) :=
      generalStageHasZeroObject (IteratedStage C (List.ofFn (fun i => d i.succ))) (d 0)
    letI : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C (List.ofFn (fun i => d i.succ)))
        (d 0)) :=
      generalStageWaldhausenCategory (IteratedStage C (List.ofFn (fun i => d i.succ))) (d 0)
    (iteratedStageOfFnSuccEquivalence C d).functor.IsWaldhausenExact ∧
      (iteratedStageOfFnSuccEquivalence C d).inverse.IsWaldhausenExact := by
  let : HasZeroObject (Stage (IteratedStage C (List.ofFn (fun i => d i.succ))) (d 0)) :=
    generalStageHasZeroObject (IteratedStage C (List.ofFn (fun i => d i.succ))) (d 0)
  let : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C (List.ofFn (fun i => d i.succ)))
      (d 0)) :=
    generalStageWaldhausenCategory (IteratedStage C (List.ofFn (fun i => d i.succ))) (d 0)
  exact ⟨((iteratedStageListEquivalence_exact C (List.ofFn_succ (f := d))).1).comp
      (iteratedStageConsEquivalence_exact C _ _).1,
    ((iteratedStageConsEquivalence_exact C _ _).2).comp
      (iteratedStageListEquivalence_exact C (List.ofFn_succ (f := d))).2⟩

/-- The actual tuple successor transport has its strict original source inverse law. -/
theorem iteratedStageOfFnSuccEquivalence_functor_inverse {r : ℕ} (d : Fin (r + 1) → ℕ) :
    (iteratedStageOfFnSuccEquivalence C d).functor ⋙
        (iteratedStageOfFnSuccEquivalence C d).inverse = 𝟭 (IteratedStage C (List.ofFn d)) := by
  dsimp [iteratedStageOfFnSuccEquivalence, Equivalence.trans]
  rw [Functor.assoc, ← Functor.assoc
    (iteratedStageConsEquivalence C _ _).functor
    (iteratedStageConsEquivalence C _ _).inverse]
  rw [iteratedStageConsEquivalence_functor_inverse, Functor.id_comp,
    iteratedStageListEquivalence_functor_inverse]

/-- The actual tuple successor transport has its strict original target inverse law. -/
theorem iteratedStageOfFnSuccEquivalence_inverse_functor {r : ℕ} (d : Fin (r + 1) → ℕ) :
    (iteratedStageOfFnSuccEquivalence C d).inverse ⋙
        (iteratedStageOfFnSuccEquivalence C d).functor =
      𝟭 (Stage (IteratedStage C (List.ofFn (fun i => d i.succ))) (d 0)) := by
  dsimp [iteratedStageOfFnSuccEquivalence, Equivalence.trans]
  rw [Functor.assoc, ← Functor.assoc
    (iteratedStageListEquivalence C (List.ofFn_succ (f := d))).inverse
    (iteratedStageListEquivalence C (List.ofFn_succ (f := d))).functor]
  rw [iteratedStageListEquivalence_inverse_functor, Functor.id_comp,
    iteratedStageConsEquivalence_inverse_functor]

universe uD vD

private structure IteratedStageFunctorData
    {C : Type (max u v)} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    {D : Type (max uD vD)} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    (ns : List ℕ) where
  functor : IteratedStage C ns ⥤ IteratedStage D ns
  exact : functor.IsWaldhausenExact

private def iteratedStageFunctorData
    {C : Type (max u v)} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    {D : Type (max uD vD)} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    {F : C ⥤ D} (hF : F.IsWaldhausenExact) :
    (ns : List ℕ) → IteratedStageFunctorData (C := C) (D := D) ns
  | [] => by
      let G : IteratedStage C [] ⥤ IteratedStage D [] := by
        dsimp [IteratedStage, iteratedStageCategory, iteratedStageData]
        exact F
      refine ⟨G, ?_⟩
      dsimp [G, IteratedStage, iteratedStageCategory, iteratedStageHasZeroObject,
        iteratedStageWaldhausenCategory, iteratedStageData]
      exact hF
  | n :: ns => by
      let M := iteratedStageFunctorData hF ns
      let G : IteratedStage C (n :: ns) ⥤ IteratedStage D (n :: ns) := by
        dsimp [IteratedStage, iteratedStageCategory, iteratedStageData]
        exact M.exact.mapStage n
      refine ⟨G, ?_⟩
      dsimp [G, IteratedStage, iteratedStageCategory, iteratedStageHasZeroObject,
        iteratedStageWaldhausenCategory, iteratedStageData]
      exact M.exact.mapStage_isWaldhausenExact n

variable {C}
variable {D : Type (max uD vD)} [Category.{vD} D] [HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- Exact-functor maps on every original iterated finite S-stage. -/
@[no_expose]
def mapIteratedStage (ns : List ℕ) : IteratedStage C ns ⥤ IteratedStage D ns :=
  (iteratedStageFunctorData hF ns).functor

/-- Exactness is earned recursively from the original exact base
functor and the genuine finite-stage preservation theorem. -/
theorem mapIteratedStage_isWaldhausenExact (ns : List ℕ) :
    (mapIteratedStage hF ns).IsWaldhausenExact := by
  unfold mapIteratedStage
  exact (iteratedStageFunctorData hF ns).exact

/-- The original input functor, viewed at zero iterations through the
literal canonical carrier and category equations. -/
@[no_expose]
def baseIteratedStageFunctor : IteratedStage C [] ⥤ IteratedStage D [] := by
  dsimp [IteratedStage, iteratedStageCategory, iteratedStageData]
  exact F

/-- At zero iterations the actual recursive map is the original functor. -/
theorem mapIteratedStage_nil : mapIteratedStage hF [] =
    baseIteratedStageFunctor (F := F) := by
  unfold mapIteratedStage iteratedStageFunctorData baseIteratedStageFunctor
  rfl

/-- The entire zero-fold map commutes with the actual original Nil
charts, as an equality of functors into the original target category. -/
theorem mapIteratedStage_nil_chart :
    mapIteratedStage hF [] ⋙ (iteratedStageNilEquivalence D).functor =
      (iteratedStageNilEquivalence C).functor ⋙ F := by
  rw [mapIteratedStage_nil]
  dsimp [baseIteratedStageFunctor, iteratedStageNilEquivalence, IteratedStage,
    iteratedStageCategory, iteratedStageHasZeroObject, iteratedStageWaldhausenCategory,
    iteratedStageData, Equivalence.refl, id]
  rfl

/-- The actual next S-stage map viewed through the canonical successor
carrier and category equations. -/
@[no_expose]
def successorIteratedStageFunctor (n : ℕ) (ns : List ℕ) :
    IteratedStage C (n :: ns) ⥤ IteratedStage D (n :: ns) := by
  dsimp [IteratedStage, iteratedStageCategory, iteratedStageData]
  exact (mapIteratedStage_isWaldhausenExact hF ns).mapStage n

/-- The successor map is the original stage map of the prior exact map. -/
theorem mapIteratedStage_cons (n : ℕ) (ns : List ℕ) :
    mapIteratedStage hF (n :: ns) = successorIteratedStageFunctor hF n ns := by
  unfold mapIteratedStage iteratedStageFunctorData successorIteratedStageFunctor
  rfl

/-- The entire successor map commutes with the actual original Cons
charts and the exact map on the original prior iteration. -/
theorem mapIteratedStage_cons_chart (n : ℕ) (ns : List ℕ) :
    letI : HasZeroObject (Stage (IteratedStage C ns) n) :=
      generalStageHasZeroObject (IteratedStage C ns) n
    letI : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C ns) n) :=
      generalStageWaldhausenCategory (IteratedStage C ns) n
    letI : HasZeroObject (Stage (IteratedStage D ns) n) :=
      generalStageHasZeroObject (IteratedStage D ns) n
    letI : WaldhausenCategoryWithoutGluing (Stage (IteratedStage D ns) n) :=
      generalStageWaldhausenCategory (IteratedStage D ns) n
    mapIteratedStage hF (n :: ns) ⋙ (iteratedStageConsEquivalence D n ns).functor =
      (iteratedStageConsEquivalence C n ns).functor ⋙
        (mapIteratedStage_isWaldhausenExact hF ns).mapStage n := by
  rw [mapIteratedStage_cons]
  dsimp [successorIteratedStageFunctor, iteratedStageConsEquivalence, IteratedStage,
    iteratedStageCategory, iteratedStageHasZeroObject, iteratedStageWaldhausenCategory,
    iteratedStageData, Equivalence.refl, id]
  rfl

private theorem stageMap_eq_of_eq {A : Type u} [Category.{v} A]
    [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    {B : Type uD} [Category.{vD} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {K L : A ⥤ B} (hK : K.IsWaldhausenExact) (hL : L.IsWaldhausenExact)
    (h : K = L) (n : ℕ) : hK.mapStage n = hL.mapStage n := by
  subst L
  rfl

/-- Every degree list sends the original identity to the actual identity. -/
theorem mapIteratedStage_id (ns : List ℕ) :
    mapIteratedStage (Functor.IsWaldhausenExact.id (C := C)) ns =
      𝟭 (IteratedStage C ns) := by
  induction ns with
  | nil =>
      unfold mapIteratedStage iteratedStageFunctorData
      rfl
  | cons n ns ih =>
      rw [mapIteratedStage_cons]
      unfold successorIteratedStageFunctor
      dsimp [IteratedStage, iteratedStageCategory, iteratedStageData]
      exact (stageMap_eq_of_eq
        (mapIteratedStage_isWaldhausenExact (Functor.IsWaldhausenExact.id (C := C)) ns)
        (Functor.IsWaldhausenExact.id (C := IteratedStage C ns)) ih n).trans
          (Functor.IsWaldhausenExact.mapStage_id (C := IteratedStage C ns) n)

universe uE vE

variable {E : Type (max uE vE)} [Category.{vE} E] [HasZeroObject E]
    [WaldhausenCategoryWithoutGluing E]
variable {G : D ⥤ E}

/-- Composition at every original finite iteration uses the same original
stage diagrams and the exactness earned at the preceding iteration. -/
theorem mapIteratedStage_comp (hG : G.IsWaldhausenExact) (ns : List ℕ) :
    mapIteratedStage (hF.comp hG) ns =
      mapIteratedStage hF ns ⋙ mapIteratedStage hG ns := by
  induction ns with
  | nil =>
      unfold mapIteratedStage iteratedStageFunctorData
      rfl
  | cons n ns ih =>
      rw [mapIteratedStage_cons, mapIteratedStage_cons, mapIteratedStage_cons]
      unfold successorIteratedStageFunctor
      dsimp [IteratedStage, iteratedStageCategory, iteratedStageData]
      exact (stageMap_eq_of_eq (mapIteratedStage_isWaldhausenExact (hF.comp hG) ns)
        ((mapIteratedStage_isWaldhausenExact hF ns).comp
          (mapIteratedStage_isWaldhausenExact hG ns)) ih n).trans
          (Functor.IsWaldhausenExact.mapStage_comp
            (mapIteratedStage_isWaldhausenExact hF ns)
            (mapIteratedStage_isWaldhausenExact hG ns) n)

/-- Exact base maps commute with literal transport between equal original degree lists. -/
theorem mapIteratedStage_list_transport {ns ms : List ℕ} (h : ns = ms) :
    mapIteratedStage hF ns ⋙ (iteratedStageListEquivalence D h).functor =
      (iteratedStageListEquivalence C h).functor ⋙ mapIteratedStage hF ms := by
  subst ms
  rfl

/-- The original tuple successor equivalences commute with the same exact
base functor mapped through the original outer stage. -/
theorem mapIteratedStage_tuple_successor {r : ℕ} (d : Fin (r + 1) → ℕ) :
    let ns := List.ofFn (fun i => d i.succ)
    letI : HasZeroObject (Stage (IteratedStage C ns) (d 0)) :=
      generalStageHasZeroObject (IteratedStage C ns) (d 0)
    letI : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C ns) (d 0)) :=
      generalStageWaldhausenCategory (IteratedStage C ns) (d 0)
    letI : HasZeroObject (Stage (IteratedStage D ns) (d 0)) :=
      generalStageHasZeroObject (IteratedStage D ns) (d 0)
    letI : WaldhausenCategoryWithoutGluing (Stage (IteratedStage D ns) (d 0)) :=
      generalStageWaldhausenCategory (IteratedStage D ns) (d 0)
    mapIteratedStage hF (List.ofFn d) ⋙ (iteratedStageOfFnSuccEquivalence D d).functor =
      (iteratedStageOfFnSuccEquivalence C d).functor ⋙
        (mapIteratedStage_isWaldhausenExact hF ns).mapStage (d 0) := by
  dsimp [iteratedStageOfFnSuccEquivalence, Equivalence.trans]
  rw [← Functor.assoc, mapIteratedStage_list_transport]
  rw [Functor.assoc]
  unfold iteratedStageConsEquivalence
  dsimp [mapIteratedStage, iteratedStageFunctorData, IteratedStage, iteratedStageCategory,
    iteratedStageData]
  rfl

variable (C)

private def IteratedStageData.successor (n : ℕ) (D : IteratedStageData.{v, max u v}) :
    IteratedStageData.{v, max u v} := by
  letI : Category.{v} D.carrier := D.category
  letI : HasZeroObject D.carrier := D.zero
  letI : WaldhausenCategoryWithoutGluing D.carrier := D.waldhausen
  letI : HasZeroObject (Stage D.carrier n) := generalStageHasZeroObject D.carrier n
  exact ⟨Stage D.carrier n, inferInstance, generalStageHasZeroObject D.carrier n,
    generalStageWaldhausenCategory D.carrier n⟩

private theorem iteratedStageData_append (ns ms : List ℕ) :
    iteratedStageData (IteratedStage C ms) ns = iteratedStageData C (ns ++ ms) := by
  induction ns with
  | nil =>
      dsimp [IteratedStage, iteratedStageCategory, iteratedStageHasZeroObject,
        iteratedStageWaldhausenCategory, iteratedStageData]
  | cons n ns ih =>
      change IteratedStageData.successor n (iteratedStageData (IteratedStage C ms) ns) =
        IteratedStageData.successor n (iteratedStageData C (ns ++ ms))
      exact congrArg (IteratedStageData.successor n) ih

private def IteratedStageData.equivalenceOfEq (D E : IteratedStageData.{v, max u v}) (h : D = E) :
    letI : Category.{v} D.carrier := D.category
    letI : Category.{v} E.carrier := E.category
    D.carrier ≌ E.carrier := by
  subst E
  letI : Category.{v} D.carrier := D.category
  exact Equivalence.refl

private theorem IteratedStageData.equivalenceOfEq_exact
    (D E : IteratedStageData.{v, max u v}) (h : D = E) :
    letI : Category.{v} D.carrier := D.category
    letI : HasZeroObject D.carrier := D.zero
    letI : WaldhausenCategoryWithoutGluing D.carrier := D.waldhausen
    letI : Category.{v} E.carrier := E.category
    letI : HasZeroObject E.carrier := E.zero
    letI : WaldhausenCategoryWithoutGluing E.carrier := E.waldhausen
    (D.equivalenceOfEq E h).functor.IsWaldhausenExact ∧
      (D.equivalenceOfEq E h).inverse.IsWaldhausenExact := by
  subst E
  let : Category.{v} D.carrier := D.category
  let : HasZeroObject D.carrier := D.zero
  let : WaldhausenCategoryWithoutGluing D.carrier := D.waldhausen
  dsimp [IteratedStageData.equivalenceOfEq, Equivalence.refl, id]
  exact ⟨Functor.IsWaldhausenExact.id, Functor.IsWaldhausenExact.id⟩

private theorem IteratedStageData.equivalenceOfEq_functor_inverse
    (D E : IteratedStageData.{v, max u v}) (h : D = E) :
    letI : Category.{v} D.carrier := D.category
    letI : Category.{v} E.carrier := E.category
    (D.equivalenceOfEq E h).functor ⋙ (D.equivalenceOfEq E h).inverse = 𝟭 D.carrier := by
  subst E
  let : Category.{v} D.carrier := D.category
  dsimp [IteratedStageData.equivalenceOfEq, Equivalence.refl, id]
  rfl

private theorem IteratedStageData.equivalenceOfEq_inverse_functor
    (D E : IteratedStageData.{v, max u v}) (h : D = E) :
    letI : Category.{v} D.carrier := D.category
    letI : Category.{v} E.carrier := E.category
    (D.equivalenceOfEq E h).inverse ⋙ (D.equivalenceOfEq E h).functor = 𝟭 E.carrier := by
  subst E
  let : Category.{v} D.carrier := D.category
  dsimp [IteratedStageData.equivalenceOfEq, Equivalence.refl, id]
  rfl

private theorem IteratedStageData.equivalenceOfEq_successor
    (D E : IteratedStageData.{v, max u v}) (h : D = E) (n : ℕ) :
    letI : Category.{v} D.carrier := D.category
    letI : HasZeroObject D.carrier := D.zero
    letI : WaldhausenCategoryWithoutGluing D.carrier := D.waldhausen
    letI : Category.{v} E.carrier := E.category
    letI : HasZeroObject E.carrier := E.zero
    letI : WaldhausenCategoryWithoutGluing E.carrier := E.waldhausen
    letI : HasZeroObject (Stage D.carrier n) := generalStageHasZeroObject D.carrier n
    letI : WaldhausenCategoryWithoutGluing (Stage D.carrier n) :=
      generalStageWaldhausenCategory D.carrier n
    letI : HasZeroObject (Stage E.carrier n) := generalStageHasZeroObject E.carrier n
    letI : WaldhausenCategoryWithoutGluing (Stage E.carrier n) :=
      generalStageWaldhausenCategory E.carrier n
    letI : Category.{v} (D.successor n).carrier := (D.successor n).category
    letI : Category.{v} (E.successor n).carrier := (E.successor n).category
    ((D.successor n).equivalenceOfEq (E.successor n) (congrArg
        (IteratedStageData.successor n) h)).functor =
      (IteratedStageData.equivalenceOfEq_exact D E h).1.mapStage n := by
  subst E
  let : Category.{v} D.carrier := D.category
  let : HasZeroObject D.carrier := D.zero
  let : WaldhausenCategoryWithoutGluing D.carrier := D.waldhausen
  dsimp [IteratedStageData.equivalenceOfEq, IteratedStageData.successor, Equivalence.refl, id]
  rfl

/-- Iteration of the actual prior S-categories is the original iteration of the concatenated degree
list. -/
@[no_expose]
def iteratedStageFlattenEquivalence (ns ms : List ℕ) :
    IteratedStage (IteratedStage C ms) ns ≌ IteratedStage C (ns ++ ms) :=
  (iteratedStageData (IteratedStage C ms) ns).equivalenceOfEq
    (iteratedStageData C (ns ++ ms)) (iteratedStageData_append C ns ms)

/-- Both directions of original degree-list flattening retain all original Waldhausen structures. -/
theorem iteratedStageFlattenEquivalence_exact (ns ms : List ℕ) :
    (iteratedStageFlattenEquivalence C ns ms).functor.IsWaldhausenExact ∧
      (iteratedStageFlattenEquivalence C ns ms).inverse.IsWaldhausenExact :=
  IteratedStageData.equivalenceOfEq_exact _ _ (iteratedStageData_append C ns ms)

/-- The actual equality-carrier flattening has its literal original source round trip. -/
theorem iteratedStageFlattenEquivalence_functor_inverse (ns ms : List ℕ) :
    (iteratedStageFlattenEquivalence C ns ms).functor ⋙
        (iteratedStageFlattenEquivalence C ns ms).inverse =
      𝟭 (IteratedStage (IteratedStage C ms) ns) :=
  IteratedStageData.equivalenceOfEq_functor_inverse _ _ (iteratedStageData_append C ns ms)

/-- The reverse equality-carrier flattening has its literal original target round trip. -/
theorem iteratedStageFlattenEquivalence_inverse_functor (ns ms : List ℕ) :
    (iteratedStageFlattenEquivalence C ns ms).inverse ⋙
        (iteratedStageFlattenEquivalence C ns ms).functor =
      𝟭 (IteratedStage C (ns ++ ms)) :=
  IteratedStageData.equivalenceOfEq_inverse_functor _ _ (iteratedStageData_append C ns ms)

set_option backward.isDefEq.respectTransparency false in
/-- Flattening no outer stages is the original nil carrier chart of the inner stage. -/
theorem iteratedStageFlattenEquivalence_nil (ms : List ℕ) :
    (iteratedStageFlattenEquivalence C [] ms).functor =
      (iteratedStageNilEquivalence (IteratedStage C ms)).functor := by
  dsimp [iteratedStageFlattenEquivalence, iteratedStageNilEquivalence,
    IteratedStage, iteratedStageCategory, iteratedStageHasZeroObject,
    iteratedStageWaldhausenCategory, iteratedStageData, IteratedStageData.equivalenceOfEq]

set_option backward.isDefEq.respectTransparency false in
/-- The original inner exact map commutes with flattening the empty outer degree list. -/
theorem iteratedStageFlattenEquivalence_map_nil (ms : List ℕ) :
    mapIteratedStage (mapIteratedStage_isWaldhausenExact hF ms) [] ⋙
        (iteratedStageFlattenEquivalence D [] ms).functor =
      (iteratedStageFlattenEquivalence C [] ms).functor ⋙ mapIteratedStage hF ms := by
  rw [mapIteratedStage_nil, iteratedStageFlattenEquivalence_nil,
    iteratedStageFlattenEquivalence_nil]
  dsimp [baseIteratedStageFunctor, iteratedStageNilEquivalence, IteratedStage,
    iteratedStageCategory, iteratedStageHasZeroObject, iteratedStageWaldhausenCategory,
    iteratedStageData, Equivalence.refl, id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Original degree-list flattening acts in the successor exactly through the original outer
S-stage. -/
theorem iteratedStageFlattenEquivalence_cons (n : ℕ) (ns ms : List ℕ) :
    letI : HasZeroObject (Stage (IteratedStage (IteratedStage C ms) ns) n) :=
      generalStageHasZeroObject (IteratedStage (IteratedStage C ms) ns) n
    letI : WaldhausenCategoryWithoutGluing (Stage (IteratedStage (IteratedStage C ms) ns) n) :=
      generalStageWaldhausenCategory (IteratedStage (IteratedStage C ms) ns) n
    letI : HasZeroObject (Stage (IteratedStage C (ns ++ ms)) n) :=
      generalStageHasZeroObject (IteratedStage C (ns ++ ms)) n
    letI : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C (ns ++ ms)) n) :=
      generalStageWaldhausenCategory (IteratedStage C (ns ++ ms)) n
    (iteratedStageFlattenEquivalence C (n :: ns) ms).functor =
      (iteratedStageConsEquivalence (IteratedStage C ms) n ns).functor ⋙
        (iteratedStageFlattenEquivalence_exact C ns ms).1.mapStage n ⋙
          (iteratedStageConsEquivalence C n (ns ++ ms)).inverse := by
  let D := iteratedStageData (IteratedStage C ms) ns
  let E := iteratedStageData C (ns ++ ms)
  have h := IteratedStageData.equivalenceOfEq_successor D E
    (iteratedStageData_append C ns ms) n
  dsimp [D, E] at h
  simpa only [List.cons_append, IteratedStageData.successor,
    iteratedStageFlattenEquivalence, iteratedStageConsEquivalence,
    IteratedStage, iteratedStageCategory, iteratedStageHasZeroObject,
    iteratedStageWaldhausenCategory, iteratedStageData, Equivalence.refl, id,
    Functor.id_comp, Functor.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
/-- Every original exact base map commutes with flattening the complete nested stage functor. -/
theorem iteratedStageFlattenEquivalence_map (ns ms : List ℕ) :
    mapIteratedStage (mapIteratedStage_isWaldhausenExact hF ms) ns ⋙
        (iteratedStageFlattenEquivalence D ns ms).functor =
      (iteratedStageFlattenEquivalence C ns ms).functor ⋙
        mapIteratedStage hF (ns ++ ms) := by
  induction ns with
  | nil => exact iteratedStageFlattenEquivalence_map_nil C hF ms
  | cons n ns ih =>
      change mapIteratedStage (mapIteratedStage_isWaldhausenExact hF ms) (n :: ns) ⋙
          (iteratedStageFlattenEquivalence D (n :: ns) ms).functor =
        (iteratedStageFlattenEquivalence C (n :: ns) ms).functor ⋙
          mapIteratedStage hF (n :: (ns ++ ms))
      let hN := mapIteratedStage_isWaldhausenExact
        (mapIteratedStage_isWaldhausenExact hF ms) ns
      let hD := (iteratedStageFlattenEquivalence_exact D ns ms).1
      let hC := (iteratedStageFlattenEquivalence_exact C ns ms).1
      let hM := mapIteratedStage_isWaldhausenExact hF (ns ++ ms)
      have hLift : hN.mapStage n ⋙ hD.mapStage n = hC.mapStage n ⋙ hM.mapStage n :=
        (Functor.IsWaldhausenExact.mapStage_comp hN hD n).symm.trans
          ((stageMap_eq_of_eq (hN.comp hD) (hC.comp hM) ih n).trans
            (Functor.IsWaldhausenExact.mapStage_comp hC hM n))
      rw [mapIteratedStage_cons, mapIteratedStage_cons,
        iteratedStageFlattenEquivalence_cons, iteratedStageFlattenEquivalence_cons]
      simpa only [hN, hD, hC, hM, successorIteratedStageFunctor,
        iteratedStageConsEquivalence, IteratedStageData.equivalenceOfEq,
        IteratedStage, iteratedStageCategory, iteratedStageHasZeroObject,
        iteratedStageWaldhausenCategory, iteratedStageData, Equivalence.refl, id,
        Functor.id_comp, Functor.comp_id] using hLift

end CategoryTheory.Waldhausen.SConstruction
