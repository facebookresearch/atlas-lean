/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanPrism

/-!
# Reindexing data for the right-comma BK prism

An arbitrary simplex operator can move the left endpoint of an outer chain.
The inner comma chain must therefore be reindexed and then pushed forward
along the outer arrow from the old left endpoint to the new one.  This file
packages that data and the exact source-functor transport required to compare
the old and reindexed comma-chain bridges.

No global prism naturality, simplicial homotopy, realization,
weak-equivalence, or Quillen-Theorem-A claim is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite Simplicial
open scoped Simplicial

namespace SSet

universe u v w hIndex

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

attribute [local instance] uliftCategory

/-- The outer chain obtained by precomposition with a reindexing functor. -/
abbrev rightCommaReindexOuter
    {D : Type u} [Category.{hIndex} D] {m n : ℕ} (s : ComposableArrows D n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) : ComposableArrows D m :=
  Φ ⋙ s

@[simp]
theorem rightCommaReindexOuter_obj
    {D : Type u} [Category.{hIndex} D] {m n : ℕ}
    (s : ComposableArrows D n) (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    (i : Fin (m + 1)) :
    (rightCommaReindexOuter s Φ).obj i = s.obj (Φ.obj i) :=
  rfl

@[simp]
theorem rightCommaReindexOuter_map
    {D : Type u} [Category.{hIndex} D] {m n : ℕ}
    (s : ComposableArrows D n) (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (rightCommaReindexOuter s Φ).map f = s.map (Φ.map f) :=
  rfl

/-- The outer-chain arrow from the old left endpoint to the left endpoint
selected by a reindexing functor. -/
def rightCommaReindexBase
    {D : Type u} [Category.{hIndex} D] {m n : ℕ} (s : ComposableArrows D n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    s.left ⟶ (rightCommaReindexOuter s Φ).left :=
  s.map (homOfLE (Fin.zero_le (Φ.obj 0)))

@[simp]
theorem rightCommaReindexBase_eq
    {D : Type u} [Category.{hIndex} D] {m n : ℕ}
    (s : ComposableArrows D n) (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    rightCommaReindexBase s Φ =
      s.map (homOfLE (Fin.zero_le (Φ.obj 0))) :=
  rfl

/-- Reindex an inner comma chain and push it forward to the new outer left
endpoint. -/
def rightCommaReindexInner (F : C ⥤ D) {m n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    ComposableArrows
      ((CostructuredArrow.functor F).obj
        (rightCommaReindexOuter s Φ).left) m := by
  change Fin (n + 1) ⥤ CostructuredArrow F s.left at X
  change Fin (m + 1) ⥤
    CostructuredArrow F (rightCommaReindexOuter s Φ).left
  exact (Φ ⋙ X) ⋙ CostructuredArrow.map
    (rightCommaReindexBase s Φ)

@[simp]
theorem rightCommaReindexInner_obj (F : C ⥤ D) {m n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) (i : Fin (m + 1)) :
    (rightCommaReindexInner F s X Φ).obj i =
      (CostructuredArrow.map (rightCommaReindexBase s Φ)).obj
        (X.obj (Φ.obj i)) :=
  rfl

theorem rightCommaReindexInner_obj_hom (F : C ⥤ D) {m n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) (i : Fin (m + 1)) :
    ((rightCommaReindexInner F s X Φ).obj i).hom =
      (X.obj (Φ.obj i)).hom ≫ rightCommaReindexBase s Φ :=
  rfl

@[simp]
theorem rightCommaReindexInner_map (F : C ⥤ D) {m n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (rightCommaReindexInner F s X Φ).map f =
      (CostructuredArrow.map (rightCommaReindexBase s Φ)).map
        (X.map (Φ.map f)) :=
  rfl

/-- Reindexing the identity composable-arrow chain by `Φ` recovers `Φ`. -/
theorem identityChain_whiskerLeft {m n : ℕ}
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    Φ ⋙ 𝟭 (Fin (n + 1)) = Φ :=
  Functor.comp_id Φ

/-- The source functor of the prewhiskered comma-chain bridge equals the
source functor constructed from the reindexed comma chain. -/
theorem rightCommaChainBridgeReindexSource_eq (F : C ⥤ D) {m n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    Φ ⋙ (X ⋙ (rightCommaProjectionFunctor.{u, v, w} F s.left ⋙ F)) =
      rightCommaReindexInner F s X Φ ⋙
        (rightCommaProjectionFunctor.{u, v, w} F
          (rightCommaReindexOuter s Φ).left ⋙ F) := by
  apply CategoryTheory.Functor.hext
  · intro i
    rfl
  · intro i j f
    exact HEq.rfl

/-- The old comma-chain bridge, prewhiskered by `Φ` and transported to the
source functor of the reindexed comma chain. -/
def rightCommaChainBridgeReindexTransport (F : C ⥤ D) {m n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    rightCommaReindexInner F s X Φ ⋙
          (rightCommaProjectionFunctor.{u, v, w} F
            (rightCommaReindexOuter s Φ).left ⋙ F) ⟶
        rightCommaReindexOuter s Φ :=
  eqToHom (rightCommaChainBridgeReindexSource_eq F s X Φ).symm ≫
    Functor.whiskerLeft Φ (rightCommaChainBridge F s X)

/-- The transported prewhiskered bridge is the bridge constructed directly
from the reindexed outer and inner chains. -/
theorem rightCommaChainBridgeReindexTransport_eq (F : C ⥤ D) {m n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    rightCommaChainBridgeReindexTransport F s X Φ =
      rightCommaChainBridge F (rightCommaReindexOuter s Φ)
        (rightCommaReindexInner F s X Φ) := by
  apply NatTrans.ext
  funext i
  let hS := rightCommaChainBridgeReindexSource_eq F s X Φ
  change (eqToHom hS.symm ≫
      Functor.whiskerLeft Φ (rightCommaChainBridge F s X)).app i =
    (rightCommaChainBridge F (rightCommaReindexOuter s Φ)
      (rightCommaReindexInner F s X Φ)).app i
  rw [NatTrans.comp_app, eqToHom_app]
  apply eq_of_heq
  rw [eqToHom_comp_heq_iff]
  rw [Functor.whiskerLeft_app]
  rw [rightCommaChainBridge_app, rightCommaChainBridge_app]
  rw [rightCommaReindexInner_obj_hom]
  apply heq_of_eq
  change (X.obj (Φ.obj i)).hom ≫
      s.map (homOfLE (Fin.zero_le (Φ.obj i))) =
    ((X.obj (Φ.obj i)).hom ≫
        s.map (homOfLE (Fin.zero_le (Φ.obj 0)))) ≫
      s.map (Φ.map (homOfLE (Fin.zero_le i)))
  rw [Category.assoc, ← s.map_comp]
  exact congrArg ((X.obj (Φ.obj i)).hom ≫ ·)
    (congrArg s.map (Subsingleton.elim _ _))

/-- Changing only the source functor of a natural transformation by equality
does not change its nerve cylinder map. -/
theorem nerveHomotopyMap_eqToHom_comp
    {J E : Type u} [Category.{v} J] [Category.{v} E]
    {A B T : J ⥤ E} (h : A = B) (α : A ⟶ T) :
    CategoryTheory.NatTrans.nerveHomotopyMap (eqToHom h.symm ≫ α) =
      CategoryTheory.NatTrans.nerveHomotopyMap α := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

/-- Equality transport of the target functor does not change the nerve
cylinder map. -/
theorem nerveHomotopyMap_comp_eqToHom
    {J E : Type u} [Category.{v} J] [Category.{v} E]
    {A B B' : J ⥤ E} (hB : B = B') (α : A ⟶ B) :
    CategoryTheory.NatTrans.nerveHomotopyMap (α ≫ eqToHom hB) =
      CategoryTheory.NatTrans.nerveHomotopyMap α := by
  cases hB
  rw [eqToHom_refl, Category.comp_id]

/-- Equality transport of both functor endpoints does not change the nerve
cylinder map. -/
theorem nerveHomotopyMap_eqToHom_comp_eqToHom
    {J E : Type u} [Category.{v} J] [Category.{v} E]
    {A A' B B' : J ⥤ E} (hA : A = A') (hB : B = B')
    (α : A ⟶ B) :
    CategoryTheory.NatTrans.nerveHomotopyMap
        ((eqToHom hA.symm ≫ α) ≫ eqToHom hB) =
      CategoryTheory.NatTrans.nerveHomotopyMap α := by
  exact (nerveHomotopyMap_comp_eqToHom hB
    (eqToHom hA.symm ≫ α)).trans
      (nerveHomotopyMap_eqToHom_comp hA α)

/-- A reindexing functor between the ambient-universe finite prism indices. -/
def rightCommaPrismReindexFunctor {m n : ℕ}
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    rightCommaPrismIndex.{u} m ⥤ rightCommaPrismIndex.{u} n where
  obj i := ULift.up (Φ.obj i.down)
  map f := Φ.map f
  map_id i := Φ.map_id i.down
  map_comp f g := Φ.map_comp f g

/-- The simplex of the lifted finite index selected by a reindexing
functor. -/
def rightCommaPrismReindexSimplex {m n : ℕ}
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    ComposableArrows (rightCommaPrismIndex.{u} n) m :=
  rightCommaPrismIndexSimplex m ⋙ rightCommaPrismReindexFunctor Φ

/-- The lifted source of the prewhiskered comma-chain bridge is the source
constructed from the reindexed comma chain. -/
theorem rightCommaChainBridgeLiftReindexSource_eq (F : C ⥤ D)
    {m n : ℕ} (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    rightCommaPrismReindexFunctor.{max u v w} Φ ⋙
        rightCommaPrismLiftChain
          (X ⋙ (rightCommaProjectionFunctor.{u, v, w} F s.left ⋙ F)) =
      rightCommaPrismLiftChain
        (rightCommaReindexInner F s X Φ ⋙
          (rightCommaProjectionFunctor.{u, v, w} F
            (rightCommaReindexOuter s Φ).left ⋙ F)) := by
  apply CategoryTheory.Functor.hext
  · intro i
    rfl
  · intro i j f
    exact HEq.rfl

/-- The lifted target of the prewhiskered bridge is the lifted reindexed
outer chain. -/
theorem rightCommaPrismLiftChain_reindexOuter_eq
    {D : Type u} [Category.{hIndex} D] {m n : ℕ}
    (s : ComposableArrows D n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    rightCommaPrismReindexFunctor.{max u hIndex} Φ ⋙ rightCommaPrismLiftChain s =
      rightCommaPrismLiftChain (rightCommaReindexOuter s Φ) := by
  apply CategoryTheory.Functor.hext
  · intro i
    rfl
  · intro i j f
    exact HEq.rfl

/-- The lifted old bridge, prewhiskered and transported to the source of the
reindexed comma chain. -/
def rightCommaChainBridgeLiftReindexTransport (F : C ⥤ D)
    {m n : ℕ} (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    rightCommaPrismLiftChain
          (rightCommaReindexInner F s X Φ ⋙
            (rightCommaProjectionFunctor.{u, v, w} F
              (rightCommaReindexOuter s Φ).left ⋙ F)) ⟶
      rightCommaPrismLiftChain (rightCommaReindexOuter s Φ) :=
  (eqToHom (rightCommaChainBridgeLiftReindexSource_eq F s X Φ).symm ≫
    Functor.whiskerLeft (rightCommaPrismReindexFunctor.{max u v w} Φ)
      (rightCommaChainBridgeLift F s X)) ≫
        eqToHom (rightCommaPrismLiftChain_reindexOuter_eq s Φ)

/-- The lifted transported bridge is the lifted bridge constructed directly
from the reindexed chains. -/
theorem rightCommaChainBridgeLiftReindexTransport_eq (F : C ⥤ D)
    {m n : ℕ} (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    rightCommaChainBridgeLiftReindexTransport F s X Φ =
      rightCommaChainBridgeLift F (rightCommaReindexOuter s Φ)
        (rightCommaReindexInner F s X Φ) := by
  apply NatTrans.ext
  funext i
  let hS := rightCommaChainBridgeLiftReindexSource_eq F s X Φ
  let hT := rightCommaPrismLiftChain_reindexOuter_eq s Φ
  unfold rightCommaChainBridgeLiftReindexTransport
  change ((eqToHom hS.symm ≫
      Functor.whiskerLeft (rightCommaPrismReindexFunctor.{max u v w} Φ)
        (rightCommaChainBridgeLift F s X)) ≫ eqToHom hT).app i = _
  simp only [NatTrans.comp_app, eqToHom_app]
  apply eq_of_heq
  rw [comp_eqToHom_heq_iff]
  rw [eqToHom_comp_heq_iff]
  rw [Functor.whiskerLeft_app]
  rw [rightCommaChainBridgeLift_app, rightCommaChainBridgeLift_app]
  rw [rightCommaReindexInner_obj_hom]
  apply heq_of_eq
  change (X.obj (Φ.obj i.down)).hom ≫
      s.map (homOfLE (Fin.zero_le (Φ.obj i.down))) =
    ((X.obj (Φ.obj i.down)).hom ≫
        s.map (homOfLE (Fin.zero_le (Φ.obj 0)))) ≫
      s.map (Φ.map (homOfLE (Fin.zero_le i.down)))
  rw [Category.assoc, ← s.map_comp]
  exact congrArg ((X.obj (Φ.obj i.down)).hom ≫ ·)
    (congrArg s.map (Subsingleton.elim _ _))

/-- Transporting the endpoint functors of the prewhiskered bridge does not
change its nerve cylinder map. -/
theorem rightCommaReindexTransport_nerveHomotopyMap
    {C D : Type u} [Category.{0} C] [Category.{0} D] (F : C ⥤ D)
    {m n : ℕ} (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    CategoryTheory.NatTrans.nerveHomotopyMap
        (rightCommaChainBridgeLiftReindexTransport F s X Φ) =
      CategoryTheory.NatTrans.nerveHomotopyMap
        (Functor.whiskerLeft (rightCommaPrismReindexFunctor Φ)
          (rightCommaChainBridgeLift F s X)) := by
  unfold rightCommaChainBridgeLiftReindexTransport
  exact nerveHomotopyMap_eqToHom_comp_eqToHom
    (rightCommaChainBridgeLiftReindexSource_eq F s X Φ)
    (rightCommaPrismLiftChain_reindexOuter_eq s Φ)
    (Functor.whiskerLeft (rightCommaPrismReindexFunctor Φ)
      (rightCommaChainBridgeLift F s X))

/-- The finite-index functor underlying a morphism in the opposite simplex
category. -/
abbrev rightCommaSimplexReindexFunctor {m n : ℕ}
    (k : op ⦋n⦌ ⟶ op ⦋m⦌) : Fin (m + 1) ⥤ Fin (n + 1) :=
  (SimplexCategory.toCat.map k.unop).toFunctor

universe uIndex vIndex uTarget vTarget

private theorem classifier_eqToHom_comp_eqToHom
    {J : Type uIndex} [Category.{vIndex} J]
    {E : Type uTarget} [Category.{vTarget} E]
    {A A' B B' : J ⥤ E} (hA : A = A') (hB : B = B') (α : A ⟶ B) :
    CategoryTheory.NatTrans.nerveCylinderFunctor
        ((eqToHom hA.symm ≫ α) ≫ eqToHom hB) =
      CategoryTheory.NatTrans.nerveCylinderFunctor α := by
  cases hA
  cases hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The degreewise right-comma prism commutes with an arbitrary simplicial
reindexing. -/
theorem rightCommaPrismSimplex_naturality (F : C ⥤ D) {m n : ℕ}
    (k : op ⦋n⦌ ⟶ op ⦋m⦌) (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (t : (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌)) :
    (nerve D).map k (rightCommaPrismSimplex F s X t) =
      rightCommaPrismSimplex F
        (rightCommaReindexOuter s (rightCommaSimplexReindexFunctor k))
        (rightCommaReindexInner F s X (rightCommaSimplexReindexFunctor k))
        ((Δ[1] : SSet.{max u v w}).map k t) := by
  let Φ := rightCommaSimplexReindexFunctor k
  let K := rightCommaPrismReindexFunctor.{max u v w} Φ
  let α := rightCommaChainBridgeLift F s X
  let αt := rightCommaChainBridgeLiftReindexTransport F s X Φ
  let α' := rightCommaChainBridgeLift F (rightCommaReindexOuter s Φ)
    (rightCommaReindexInner F s X Φ)
  let Iₙ := rightCommaPrismIndexSimplex.{max u v w} n
  let Iₘ := rightCommaPrismIndexSimplex.{max u v w} m
  let Tₙ := (SSet.stdSimplex.asOrderHom t).toFunctor
  let Tₘ := (SSet.stdSimplex.asOrderHom ((Δ[1] : SSet.{max u v w}).map k t)).toFunctor
  have hTransport : CategoryTheory.NatTrans.nerveCylinderFunctor αt =
      CategoryTheory.NatTrans.nerveCylinderFunctor (Functor.whiskerLeft K α) := by
    dsimp only [αt, rightCommaChainBridgeLiftReindexTransport]
    exact classifier_eqToHom_comp_eqToHom
      (rightCommaChainBridgeLiftReindexSource_eq F s X Φ)
      (rightCommaPrismLiftChain_reindexOuter_eq s Φ) (Functor.whiskerLeft K α)
  have hBridge : CategoryTheory.NatTrans.nerveCylinderFunctor αt =
      CategoryTheory.NatTrans.nerveCylinderFunctor α' :=
    congrArg CategoryTheory.NatTrans.nerveCylinderFunctor
      (rightCommaChainBridgeLiftReindexTransport_eq F s X Φ)
  have hCyl : CategoryTheory.NatTrans.nerveCylinderFunctor α' =
      (K.prod (𝟭 (Fin 2))) ⋙ CategoryTheory.NatTrans.nerveCylinderFunctor α :=
    hBridge.symm.trans (hTransport.trans
      (CategoryTheory.NatTrans.nerveCylinderFunctor_whiskerLeft K α))
  have hInput : Φ ⋙ (Iₙ.prod' Tₙ) = (Iₘ.prod' Tₘ) ⋙ K.prod (𝟭 (Fin 2)) := by
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      exact HEq.rfl
  change Φ ⋙ ((Iₙ.prod' Tₙ) ⋙ CategoryTheory.NatTrans.nerveCylinderFunctor α) =
    (Iₘ.prod' Tₘ) ⋙ CategoryTheory.NatTrans.nerveCylinderFunctor α'
  rw [hCyl]
  calc
    _ = (Φ ⋙ (Iₙ.prod' Tₙ)) ⋙ CategoryTheory.NatTrans.nerveCylinderFunctor α :=
      (Functor.assoc Φ (Iₙ.prod' Tₙ) _).symm
    _ = ((Iₘ.prod' Tₘ) ⋙ K.prod (𝟭 (Fin 2))) ⋙
        CategoryTheory.NatTrans.nerveCylinderFunctor α := congrArg (· ⋙ _) hInput
    _ = _ := Functor.assoc (Iₘ.prod' Tₘ) (K.prod (𝟭 (Fin 2))) _

end SSet

end
