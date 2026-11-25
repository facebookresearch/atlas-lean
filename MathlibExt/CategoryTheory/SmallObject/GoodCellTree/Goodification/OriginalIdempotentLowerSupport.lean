/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.IdempotentCoequalizerSplit

/-!
# Original lower supports carrying the endpoint idempotent

The lower objects, comparison maps and endpoint legs are the original chosen
ones. Compatible idempotents glue through the actual lower-union pushout.
Their split images use the same chosen coequalizers of the idempotent and
identity. This is the local geometry in the support-history construction of
Lurie's Higher Topos Theory, Appendix A.1.5.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalIdempotentLowerSupport

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X : C}
  {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (q : T.endpointObj ⟶ T.endpointObj)

/-- The literal chosen lower-to-original-endpoint map. -/
abbrev endpointLeg (B : LowerSet P) : L.obj B ⟶ T.endpointObj :=
  L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom

@[reassoc]
theorem map_endpointLeg {B D : LowerSet P} (h : B ≤ D) :
    L.map h ≫ endpointLeg T L D = endpointLeg T L B := by
  simp only [endpointLeg, L.map_comp_assoc]

/-- A real original lower support and its actual endpoint-compatible idempotent. -/
structure State where
  /-- The original downward-closed label support. -/
  support : LowerSet P
  /-- The idempotent on the chosen original lower object. -/
  e : L.obj support ⟶ L.obj support
  idempotent : e ≫ e = e
  endpoint : e ≫ endpointLeg T L support = endpointLeg T L support ≫ q

namespace State

variable {T L q}

/-- An inclusion retains the original lower map and its full idempotent square. -/
-- Kept in `Type`: it is the Hom type of the state category in `OriginalIdempotentSupportHistory`.
@[nolint structureInType]
structure Inclusion (A B : State T L q) : Type where
  le : A.support ≤ B.support
  commutes : A.e ≫ L.map le = L.map le ≫ B.e

namespace Inclusion

variable {A B D : State T L q}

/-- The original support inclusion and idempotent square from a state to itself. -/
def identity (A : State T L q) : Inclusion A A where
  le := le_rfl
  commutes := by rw [L.map_id]; simp

/-- Compose the original lower inclusions and their idempotent squares. -/
def comp (a : Inclusion A B) (b : Inclusion B D) : Inclusion A D where
  le := a.le.trans b.le
  commutes := by
    rw [← L.map_comp a.le b.le, ← Category.assoc, a.commutes,
      Category.assoc, b.commutes, ← Category.assoc]

instance : Subsingleton (Inclusion A B) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

end Inclusion

/-- The empty original lower object has its identity idempotent. -/
def empty : State T L q where
  support := ⊥
  e := 𝟙 _
  idempotent := Category.id_comp _
  endpoint := by
    apply L.isInitialObjBot.hom_ext

/-- The actual coequalizer split image under the same original source. -/
abbrev splitObj (A : State T L q) [HasCoequalizer A.e (𝟙 (L.obj A.support))] : Under X :=
  IdempotentCoequalizerSplit.obj A.e

/-- The actual selected inclusion of the split image into the original lower object. -/
abbrev inclusion (A : State T L q) [HasCoequalizer A.e (𝟙 (L.obj A.support))] :
    splitObj A ⟶ L.obj A.support :=
  IdempotentCoequalizerSplit.inclusion A.e A.idempotent

/-- The actual selected projection of the original lower object onto its split image. -/
abbrev projection (A : State T L q) [HasCoequalizer A.e (𝟙 (L.obj A.support))] :
    L.obj A.support ⟶ splitObj A :=
  IdempotentCoequalizerSplit.projection A.e

theorem inclusion_projection (A : State T L q)
    [HasCoequalizer A.e (𝟙 (L.obj A.support))] :
    inclusion A ≫ projection A = 𝟙 (splitObj A) :=
  IdempotentCoequalizerSplit.inclusion_projection A.e A.idempotent

theorem projection_inclusion (A : State T L q)
    [HasCoequalizer A.e (𝟙 (L.obj A.support))] :
    projection A ≫ inclusion A = A.e :=
  IdempotentCoequalizerSplit.projection_inclusion A.e A.idempotent

/-- The literal original inclusion induces a map of its actual chosen split images. -/
abbrev splitMap {A B : State T L q} (h : Inclusion A B)
    [HasCoequalizer A.e (𝟙 (L.obj A.support))]
    [HasCoequalizer B.e (𝟙 (L.obj B.support))] : splitObj A ⟶ splitObj B :=
  IdempotentCoequalizerSplit.map A.e B.e (L.map h.le) h.commutes

@[reassoc]
theorem projection_splitMap {A B : State T L q} (h : Inclusion A B)
    [HasCoequalizer A.e (𝟙 (L.obj A.support))]
    [HasCoequalizer B.e (𝟙 (L.obj B.support))] :
    projection A ≫ splitMap h = L.map h.le ≫ projection B :=
  IdempotentCoequalizerSplit.projection_map A.e B.e (L.map h.le) h.commutes

@[reassoc]
theorem splitMap_inclusion {A B : State T L q} (h : Inclusion A B)
    [HasCoequalizer A.e (𝟙 (L.obj A.support))]
    [HasCoequalizer B.e (𝟙 (L.obj B.support))] :
    splitMap h ≫ inclusion B = inclusion A ≫ L.map h.le :=
  IdempotentCoequalizerSplit.map_inclusion A.e A.idempotent B.e B.idempotent
    (L.map h.le) h.commutes

end State

variable {T L q}

/-- Compatible actual idempotents on the literal original lower intersection. -/
structure Intersection (A B : State T L q) where
  /-- The idempotent on the literal intersection of the two original lower supports. -/
  e : L.obj (A.support ⊓ B.support) ⟶ L.obj (A.support ⊓ B.support)
  idempotent : e ≫ e = e
  left : e ≫ L.map (inf_le_left : A.support ⊓ B.support ≤ A.support) =
    L.map inf_le_left ≫ A.e
  right : e ≫ L.map (inf_le_right : A.support ⊓ B.support ≤ B.support) =
    L.map inf_le_right ≫ B.e

namespace Intersection

variable {A B : State T L q} (E : Intersection A B)

theorem agreement (E : Intersection A B) :
    L.map (inf_le_left : A.support ⊓ B.support ≤ A.support) ≫
        (A.e ≫ L.map (le_sup_left : A.support ≤ A.support ⊔ B.support)) =
      L.map (inf_le_right : A.support ⊓ B.support ≤ B.support) ≫
        (B.e ≫ L.map (le_sup_right : B.support ≤ A.support ⊔ B.support)) := by
  rw [← Category.assoc, ← E.left, Category.assoc, L.map_comp,
    ← Category.assoc, ← E.right, Category.assoc, L.map_comp]

/-- The original pushout descender glues the two idempotents. -/
def union : State T L q where
  support := A.support ⊔ B.support
  e := L.unionDesc (A.e ≫ L.map le_sup_left) (B.e ≫ L.map le_sup_right) E.agreement
  idempotent := by
    apply (L.union_isPushout A.support B.support).hom_ext
    · rw [← Category.assoc, L.map_left_unionDesc, Category.assoc,
        L.map_left_unionDesc, ← Category.assoc, A.idempotent]
    · rw [← Category.assoc, L.map_right_unionDesc, Category.assoc,
        L.map_right_unionDesc, ← Category.assoc, B.idempotent]
  endpoint := by
    apply (L.union_isPushout A.support B.support).hom_ext
    · rw [← Category.assoc, L.map_left_unionDesc, Category.assoc,
        map_endpointLeg, A.endpoint, ← Category.assoc, map_endpointLeg]
    · rw [← Category.assoc, L.map_right_unionDesc, Category.assoc,
        map_endpointLeg, B.endpoint, ← Category.assoc, map_endpointLeg]

/-- The old first support and its original map survive the union construction. -/
def leftInclusion : State.Inclusion A E.union where
  le := le_sup_left
  commutes := (L.map_left_unionDesc _ _ E.agreement).symm

/-- The old second support and its original map survive the union construction. -/
def rightInclusion : State.Inclusion B E.union where
  le := le_sup_right
  commutes := (L.map_right_unionDesc _ _ E.agreement).symm

/-- The intersection itself retains its actual original endpoint map. -/
def state : State T L q where
  support := A.support ⊓ B.support
  e := E.e
  idempotent := E.idempotent
  endpoint := by
    rw [← map_endpointLeg T L (inf_le_left : A.support ⊓ B.support ≤ A.support),
      ← Category.assoc, E.left, Category.assoc, A.endpoint, ← Category.assoc]

/-- The original inclusion from the intersection state to the first lower state. -/
def toLeft : State.Inclusion E.state A where
  le := inf_le_left
  commutes := E.left

/-- The original inclusion from the intersection state to the second lower state. -/
def toRight : State.Inclusion E.state B where
  le := inf_le_right
  commutes := E.right

end Intersection

end CategoryTheory.SmallObject.OriginalIdempotentLowerSupport
