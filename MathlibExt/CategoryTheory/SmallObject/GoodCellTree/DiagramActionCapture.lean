/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.EndpointDiagramTransport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RootChangeCapture
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramActionConstraintBounds

/-!
# First original diagram factors through the same chosen lower pieces

Each original incoming arrow is factored from a source compact under its
own original root. The selected common target support contains the seed,
and every factor retains both original root and endpoint equations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t uD vD uC vC

namespace CategoryTheory.SmallObject.DiagramActionCapture

open CategoryTheory.Limits BoundedLowerSupport

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)

/-- The entire original family of bounded lower supports at the given rank. -/
abbrev Supports (chi : Cardinal.{w}) := ∀ d : D, Carrier chi (P := P d)

/-- The same original lower-colimit object under its original source root. -/
abbrev piece (d : D) (B : LowerSet (P d)) : Under (F.obj d) := (L d).obj B

/-- The original lower leg followed by the actual original component comparison. -/
def legUnder (d : D) (B : LowerSet (P d)) :
    piece theta L d B ⟶ Under.mk (f.app d) :=
  EndpointDiagramTransport.lowerLeg theta L d B ≫ (theta.component d).endpointIso.hom

/-- The literal right component of that same original under-root leg. -/
abbrev leg (d : D) (B : LowerSet (P d)) := (legUnder theta L d B).right

theorem leg_root (d : D) (B : LowerSet (P d)) :
    (piece theta L d B).hom ≫ leg theta L d B = f.app d :=
  Under.w (legUnder theta L d B)

/-- Actual original support inclusions preserve the entire target leg. -/
@[reassoc]
theorem inclusion_leg (d : D) {B E : LowerSet (P d)} (h : B ≤ E) :
    ((L d).map h).right ≫ leg theta L d E = leg theta L d B := by
  have hUnder : (L d).map h ≫ legUnder theta L d E = legUnder theta L d B := by
    dsimp only [legUnder, EndpointDiagramTransport.lowerLeg]
    simp only [Category.assoc, (L d).map_comp_assoc]
  exact congrArg Under.Hom.right hUnder

/-- The original inverse/hom functions convert the given tree action to its original target. -/
theorem lowerAction_to_original {d e : D} (g : d ⟶ e) (B : LowerSet (P d)) :
    EndpointDiagramTransport.lowerAction theta L g B ≫
        (theta.component e).endpointIso.hom.right = leg theta L d B ≫ G.map g := by
  simp only [EndpointDiagramTransport.lowerAction, EndpointDiagramTransport.action,
    leg, legUnder, Under.comp_right, Category.assoc, Under.inv_right_hom_right, Under.mk_right,
    Category.comp_id]

/-- Original raw factors with both genuine root and endpoint certificates. -/
structure Factors (chi : Cardinal.{w}) (B E : Supports (P := P) chi) where
  /-- The actual factor of each original Hom value. -/
  map {d e : D} (g : d ⟶ e) :
    (piece theta L d (B d).1).right ⟶ (piece theta L e (E e).1).right
  /-- Its actual original source-root equation. -/
  root {d e : D} (g : d ⟶ e) :
    (piece theta L d (B d).1).hom ≫ map g =
      F.map g ≫ (piece theta L e (E e).1).hom
  /-- Its actual original target comparison equation. -/
  endpoint {d e : D} (g : d ⟶ e) :
    map g ≫ leg theta L e (E e).1 = leg theta L d (B d).1 ≫ G.map g

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hArrow : HasCardinalLT (Arrow D) chi)
  (good : ∀ d, (theta.component d).tree.IsGood chi)

include hArrow good in
/-- Internally choose factors of every original arrow on one next support per target. -/
theorem existsFirstFactors (B : Supports (P := P) chi) :
    ∃ E : Supports (P := P) chi, (∀ d, B d ≤ E d) ∧
      Nonempty (Factors theta L chi B E) := by
  have h (e : D) :
      ∃ E : Carrier chi (P := P e), B e ≤ E ∧
        ∃ a : ∀ b : Over e,
          (piece theta L b.left (B b.left).1).right ⟶ ((L e).obj E.1).right,
          ∀ b : Over e,
            (piece theta L b.left (B b.left).1).hom ≫ a b =
                F.map b.hom ≫ ((L e).obj E.1).hom ∧
              a b ≫ leg theta L e E.1 =
                leg theta L b.left (B b.left).1 ≫ G.map b.hom := by
    let roots : Over e → C := fun b => F.obj b.left
    let sources : ∀ b : Over e, Under (roots b) :=
      fun b => piece theta L b.left (B b.left).1
    let : ∀ b : Over e, IsCardinalPresentable (sources b) chi := fun b =>
      RelativeCellPresentability.selectedLower chi (theta.component b.left).tree
        (good b.left) (L b.left) (B b.left).1 (B b.left).2
    let raw : ∀ b : Over e, (sources b).right ⟶ (theta.component e).tree.endpointObj.right :=
      fun b => EndpointDiagramTransport.lowerAction theta L b.hom (B b.left).1
    have raw_root (b : Over e) :
        (sources b).hom ≫ raw b = F.map b.hom ≫ (theta.component e).tree.hom :=
      EndpointDiagramTransport.lowerAction_root theta L b.hom (B b.left).1
    obtain ⟨E, hBE, _, a, ha⟩ := RootChangeCapture.existsTreeFactorFamily chi
      (theta.component e).tree (good e) (L e)
      (DiagramActionConstraintBounds.incomingLt chi hArrow e)
      roots (fun b => F.map b.hom) sources raw raw_root (B e) (fun _ => B e)
    refine ⟨E, hBE, a, ?_⟩
    intro b
    refine ⟨(ha b).1, ?_⟩
    have hb := congrArg
      (fun k : (sources b).right ⟶ (theta.component e).tree.endpointObj.right =>
        k ≫ (theta.component e).endpointIso.hom.right) (ha b).2
    calc
      a b ≫ leg theta L e E.1 =
          (a b ≫ ((L e).map (le_top : E.1 ≤ ⊤) ≫
            ((theta.component e).tree.endpointIso (L e)).hom).right) ≫
              (theta.component e).endpointIso.hom.right := by
        simp only [leg, legUnder, EndpointDiagramTransport.lowerLeg,
          Under.comp_right, Category.assoc]
      _ = raw b ≫ (theta.component e).endpointIso.hom.right := hb
      _ = leg theta L b.left (B b.left).1 ≫ G.map b.hom :=
        lowerAction_to_original theta L b.hom (B b.left).1
  choose E hBE a ha using h
  refine ⟨E, hBE, ⟨?_⟩⟩
  exact
    { map := fun {d e} g => a e (Over.mk g)
      root := fun g => (ha _ (Over.mk g)).1
      endpoint := fun g => (ha _ (Over.mk g)).2 }




/-- Every inclusion is the same right component of the selected lower comparison. -/
abbrev inclusion {chi : Cardinal.{w}} {B E : Supports (P := P) chi}
    (h : ∀ d, B d ≤ E d) (d : D) :
    (piece theta L d (B d).1).right ⟶ (piece theta L d (E d).1).right :=
  ((L d).map (h d)).right

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- The actual original lower comparison retains its original root. -/
theorem inclusion_root {chi : Cardinal.{w}} {B E : Supports (P := P) chi}
    (h : ∀ d, B d ≤ E d) (d : D) :
    (piece theta L d (B d).1).hom ≫ inclusion theta L h d =
      (piece theta L d (E d).1).hom :=
  Under.w ((L d).map (h d))

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- The same original target inverse recovers the tree endpoint leg. -/
theorem leg_to_tree (d : D) (B : LowerSet (P d)) :
    leg theta L d B ≫ (theta.component d).endpointIso.inv.right =
      (EndpointDiagramTransport.lowerLeg theta L d B).right := by
  change ((EndpointDiagramTransport.lowerLeg theta L d B).right ≫
    (theta.component d).endpointIso.hom.right) ≫
      (theta.component d).endpointIso.inv.right = _
  rw [Category.assoc, Under.hom_right_inv_right, Category.comp_id]

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- An equality at the original target gives the equality needed by native tree capture. -/
theorem originalEndpoint_eq_to_tree (d : D) {A : C} (B : LowerSet (P d))
    (p q : A ⟶ (piece theta L d B).right)
    (he : p ≫ leg theta L d B = q ≫ leg theta L d B) :
    p ≫ (EndpointDiagramTransport.lowerLeg theta L d B).right =
      q ≫ (EndpointDiagramTransport.lowerLeg theta L d B).right := by
  have h := congrArg (fun k : A ⟶ G.obj d =>
    k ≫ (theta.component d).endpointIso.inv.right) he
  simpa only [Category.assoc, leg_to_tree] using h

/-- Extend the same factors using the actual selected target comparisons. -/
def Factors.extend {chi : Cardinal.{w}} {B E Q : Supports (P := P) chi}
    (a : Factors theta L chi B E) (h : ∀ d, E d ≤ Q d) :
    Factors theta L chi B Q where
  map g := a.map g ≫ inclusion theta L h _
  root g := RootChangeCapture.extend_root (F.map g) (L _) (h _) (a.map g) (a.root g)
  endpoint g := by
    change (a.map g ≫ ((L _).map (h _)).right) ≫ leg theta L _ _ = _
    rw [Category.assoc, inclusion_leg]
    exact a.endpoint g

/-- An internally chosen first capture after forcing its identity maps. -/
structure UnitalStage (chi : Cardinal.{w}) (B : Supports (P := P) chi) where
  /-- Its same original next support family. -/
  target : Supports (P := P) chi
  /-- Every supplied original seed is included. -/
  le : ∀ d, B d ≤ target d
  /-- Every original arrow has its actual two factor equations. -/
  factors : Factors theta L chi B target
  /-- The identity factor is the actual selected stage inclusion. -/
  unit (d : D) : factors.map (𝟙 d) = inclusion theta L le d

include hArrow good in
/-- Force the unit maps by actual compact-source eventual equality. -/
theorem nonemptyUnitalStage (B : Supports (P := P) chi) :
    Nonempty (UnitalStage theta L chi B) := by
  obtain ⟨E, hBE, ⟨a⟩⟩ := existsFirstFactors theta L chi hArrow good B
  have h (e : D) : ∃ Q : Carrier chi (P := P e), ∃ hEQ : E e ≤ Q,
      a.map (𝟙 e) ≫ ((L e).map hEQ).right =
        ((L e).map (hBE e)).right ≫ ((L e).map hEQ).right := by
    let roots : PUnit.{1} → C := fun _ => F.obj e
    let sources : ∀ i : PUnit.{1}, Under (roots i) :=
      fun _ => piece theta L e (B e).1
    let : IsCardinalPresentable (piece theta L e (B e).1) chi :=
      RelativeCellPresentability.selectedLower chi (theta.component e).tree
        (good e) (L e) (B e).1 (B e).2
    let p : ∀ i : PUnit.{1}, (sources i).right ⟶ ((L e).obj (E e).1).right :=
      fun _ => a.map (𝟙 e)
    let q : ∀ i : PUnit.{1}, (sources i).right ⟶ ((L e).obj (E e).1).right :=
      fun _ => ((L e).map (hBE e)).right
    have hp (i : PUnit.{1}) :
        (sources i).hom ≫ p i = (𝟙 (F.obj e)) ≫ ((L e).obj (E e).1).hom := by
      simpa only [sources, roots, p, F.map_id, Category.id_comp] using a.root (𝟙 e)
    have hq (i : PUnit.{1}) :
        (sources i).hom ≫ q i = (𝟙 (F.obj e)) ≫ ((L e).obj (E e).1).hom := by
      simpa only [sources, roots, q, Category.id_comp] using Under.w ((L e).map (hBE e))
    have he (i : PUnit.{1}) :
        p i ≫ (EndpointDiagramTransport.lowerLeg theta L e (E e).1).right =
          q i ≫ (EndpointDiagramTransport.lowerLeg theta L e (E e).1).right := by
      apply originalEndpoint_eq_to_tree theta L e (E e).1 (p i) (q i)
      calc
        p i ≫ leg theta L e (E e).1 = leg theta L e (B e).1 ≫ G.map (𝟙 e) :=
          a.endpoint (𝟙 e)
        _ = leg theta L e (B e).1 := by
          rw [G.map_id]
          exact Category.comp_id _
        _ = q i ≫ leg theta L e (E e).1 := (inclusion_leg theta L e (hBE e)).symm
    obtain ⟨Q, _, _, hEQ, hEq⟩ := RootChangeCapture.existsTreeEqualityFamily chi
      (theta.component e).tree (good e) (L e)
      (hasCardinalLT_of_finite PUnit.{1} chi (Fact.out : chi.IsRegular).aleph0_le)
      roots (fun _ => 𝟙 (F.obj e)) sources (E e) (E e) (fun _ => E e) p q hp hq he
    exact ⟨Q, hEQ, (hEq PUnit.unit).2.2⟩
  choose Q hEQ hEq using h
  refine ⟨{
    target := Q
    le := fun d => (hBE d).trans (hEQ d)
    factors := Factors.extend theta L a hEQ
    unit := ?_ }⟩
  intro d
  change a.map (𝟙 d) ≫ ((L d).map (hEQ d)).right =
    ((L d).map ((hBE d).trans (hEQ d))).right
  calc
    _ = ((L d).map (hBE d)).right ≫ ((L d).map (hEQ d)).right := hEq d
    _ = _ := congrArg Under.Hom.right ((L d).map_comp (hBE d) (hEQ d))

/-- A new stage forces unit, ladder and delayed composition from raw previous factors. -/
structure RefinedStage (chi : Cardinal.{w}) (Bprev Bnow : Supports (P := P) chi)
    (hPrev : ∀ d, Bprev d ≤ Bnow d) (old : Factors theta L chi Bprev Bnow) where
  /-- The actual newly selected original support family. -/
  target : Supports (P := P) chi
  /-- Its actual comparison from the original current supports. -/
  le : ∀ d, Bnow d ≤ target d
  /-- The captured original arrows, extended by the same target comparison. -/
  factors : Factors theta L chi Bnow target
  /-- Every identity arrow is the same selected inclusion. -/
  unit (d : D) : factors.map (𝟙 d) = inclusion theta L le d
  /-- Successive original arrows agree after the same original source and target comparisons. -/
  ladder {d e : D} (g : d ⟶ e) :
    old.map g ≫ inclusion theta L le e = inclusion theta L hPrev d ≫ factors.map g
  /-- Delayed composition keeps the old source and the actual new middle factor. -/
  composition {d m e : D} (g : d ⟶ m) (h : m ⟶ e) :
    old.map g ≫ factors.map h = old.map (g ≫ h) ≫ inclusion theta L le e

include hArrow good in
/-- All original constraints are forced on one actually larger support per target. -/
theorem nonemptyRefinedStage (Bprev Bnow : Supports (P := P) chi)
    (hPrev : ∀ d, Bprev d ≤ Bnow d) (old : Factors theta L chi Bprev Bnow) :
    Nonempty (RefinedStage theta L chi Bprev Bnow hPrev old) := by
  obtain ⟨E, hNowE, ⟨a⟩⟩ := existsFirstFactors theta L chi hArrow good Bnow
  have h (e : D) : ∃ Q : Carrier chi (P := P e), ∃ hEQ : E e ≤ Q,
      (a.map (𝟙 e) ≫ ((L e).map hEQ).right =
        ((L e).map (hNowE e)).right ≫ ((L e).map hEQ).right) ∧
      (∀ b : Over e,
        (old.map b.hom ≫ inclusion theta L hNowE e) ≫ ((L e).map hEQ).right =
          (inclusion theta L hPrev b.left ≫ a.map b.hom) ≫ ((L e).map hEQ).right) ∧
      (∀ p : DiagramActionConstraintBounds.IncomingPair e,
        (old.map p.2.hom ≫ a.map p.1.hom) ≫ ((L e).map hEQ).right =
          (old.map (p.2.hom ≫ p.1.hom) ≫ inclusion theta L hNowE e) ≫
            ((L e).map hEQ).right) := by
    let roots : DiagramActionConstraintBounds.Constraint e → C := fun i => match i with
      | .inl _ => F.obj e
      | .inr (.inl b) => F.obj b.left
      | .inr (.inr p) => F.obj p.2.left
    let rhos : ∀ i, roots i ⟶ F.obj e := fun i => match i with
      | .inl _ => 𝟙 (F.obj e)
      | .inr (.inl b) => F.map b.hom
      | .inr (.inr p) => F.map (p.2.hom ≫ p.1.hom)
    let sources : ∀ i, Under (roots i) := fun i => match i with
      | .inl _ => piece theta L e (Bnow e).1
      | .inr (.inl b) => piece theta L b.left (Bprev b.left).1
      | .inr (.inr p) => piece theta L p.2.left (Bprev p.2.left).1
    let (i : DiagramActionConstraintBounds.Constraint e) :
        IsCardinalPresentable (sources i) chi := by
      rcases i with _ | (b | p)
      · exact RelativeCellPresentability.selectedLower chi (theta.component e).tree
          (good e) (L e) (Bnow e).1 (Bnow e).2
      · exact RelativeCellPresentability.selectedLower chi (theta.component b.left).tree
          (good b.left) (L b.left) (Bprev b.left).1 (Bprev b.left).2
      · exact RelativeCellPresentability.selectedLower chi (theta.component p.2.left).tree
          (good p.2.left) (L p.2.left) (Bprev p.2.left).1 (Bprev p.2.left).2
    let p : ∀ i, (sources i).right ⟶ ((L e).obj (E e).1).right := fun i => match i with
      | .inl _ => a.map (𝟙 e)
      | .inr (.inl b) => old.map b.hom ≫ inclusion theta L hNowE e
      | .inr (.inr p) => old.map p.2.hom ≫ a.map p.1.hom
    let q : ∀ i, (sources i).right ⟶ ((L e).obj (E e).1).right := fun i => match i with
      | .inl _ => inclusion theta L hNowE e
      | .inr (.inl b) => inclusion theta L hPrev b.left ≫ a.map b.hom
      | .inr (.inr p) => old.map (p.2.hom ≫ p.1.hom) ≫ inclusion theta L hNowE e
    have hp (i) : (sources i).hom ≫ p i = rhos i ≫ ((L e).obj (E e).1).hom := by
      rcases i with _ | (b | z)
      · simpa only [sources, p, rhos, roots, F.map_id, Category.id_comp] using a.root (𝟙 e)
      · change (piece theta L b.left (Bprev b.left).1).hom ≫
          (old.map b.hom ≫ inclusion theta L hNowE e) = _
        rw [← Category.assoc, old.root, Category.assoc, inclusion_root]
      · change (piece theta L z.2.left (Bprev z.2.left).1).hom ≫
          (old.map z.2.hom ≫ a.map z.1.hom) =
            F.map (z.2.hom ≫ z.1.hom) ≫ ((L e).obj (E e).1).hom
        rw [← Category.assoc, old.root, Category.assoc, a.root, F.map_comp]
        simp only [Category.assoc]
    have hq (i) : (sources i).hom ≫ q i = rhos i ≫ ((L e).obj (E e).1).hom := by
      rcases i with _ | (b | z)
      · simpa only [sources, q, rhos, roots, Category.id_comp] using inclusion_root theta L hNowE e
      · change (piece theta L b.left (Bprev b.left).1).hom ≫
          (inclusion theta L hPrev b.left ≫ a.map b.hom) = _
        rw [← Category.assoc, inclusion_root, a.root]
      · change (piece theta L z.2.left (Bprev z.2.left).1).hom ≫
          (old.map (z.2.hom ≫ z.1.hom) ≫ inclusion theta L hNowE e) = _
        rw [← Category.assoc, old.root, Category.assoc, inclusion_root]
    have heOriginal (i) : p i ≫ leg theta L e (E e).1 = q i ≫ leg theta L e (E e).1 := by
      rcases i with _ | (b | z)
      · change a.map (𝟙 e) ≫ leg theta L e (E e).1 =
          inclusion theta L hNowE e ≫ leg theta L e (E e).1
        rw [a.endpoint, G.map_id]
        exact (Category.comp_id _).trans (inclusion_leg theta L e (hNowE e)).symm
      · change (old.map b.hom ≫ inclusion theta L hNowE e) ≫ leg theta L e (E e).1 =
          (inclusion theta L hPrev b.left ≫ a.map b.hom) ≫ leg theta L e (E e).1
        simp only [inclusion, Category.assoc, inclusion_leg, inclusion_leg_assoc,
          old.endpoint, a.endpoint]
      · change (old.map z.2.hom ≫ a.map z.1.hom) ≫ leg theta L e (E e).1 =
          (old.map (z.2.hom ≫ z.1.hom) ≫ inclusion theta L hNowE e) ≫ leg theta L e (E e).1
        calc
          _ = old.map z.2.hom ≫ (a.map z.1.hom ≫ leg theta L e (E e).1) :=
            Category.assoc _ _ _
          _ = old.map z.2.hom ≫ (leg theta L z.1.left (Bnow z.1.left).1 ≫
              G.map z.1.hom) := by rw [a.endpoint]
          _ = (old.map z.2.hom ≫ leg theta L z.1.left (Bnow z.1.left).1) ≫
              G.map z.1.hom := (Category.assoc _ _ _).symm
          _ = (leg theta L z.2.left (Bprev z.2.left).1 ≫ G.map z.2.hom) ≫
              G.map z.1.hom := by rw [old.endpoint]
          _ = leg theta L z.2.left (Bprev z.2.left).1 ≫
              G.map (z.2.hom ≫ z.1.hom) := by rw [G.map_comp, Category.assoc]
          _ = _ := by rw [Category.assoc, inclusion_leg, old.endpoint]
    have he (i) :
        p i ≫ (EndpointDiagramTransport.lowerLeg theta L e (E e).1).right =
          q i ≫ (EndpointDiagramTransport.lowerLeg theta L e (E e).1).right :=
      originalEndpoint_eq_to_tree theta L e (E e).1 (p i) (q i) (heOriginal i)
    obtain ⟨Q, _, _, hEQ, hEq⟩ := RootChangeCapture.existsTreeEqualityFamily chi
      (theta.component e).tree (good e) (L e)
      (DiagramActionConstraintBounds.constraintLt chi hArrow e)
      roots rhos sources (E e) (E e) (fun _ => E e) p q hp hq he
    refine ⟨Q, hEQ, (hEq (.inl PUnit.unit)).2.2, ?_, ?_⟩
    · intro b
      exact (hEq (.inr (.inl b))).2.2
    · intro z
      exact (hEq (.inr (.inr z))).2.2
  choose Q hEQ hUnit hLadder hComp using h
  let hNowQ : ∀ d, Bnow d ≤ Q d := fun d => (hNowE d).trans (hEQ d)
  have comparison (e : D) :
      inclusion theta L hNowE e ≫ ((L e).map (hEQ e)).right =
        inclusion theta L hNowQ e :=
    congrArg Under.Hom.right ((L e).map_comp (hNowE e) (hEQ e))
  refine ⟨{
    target := Q
    le := hNowQ
    factors := Factors.extend theta L a hEQ
    unit := ?_
    ladder := ?_
    composition := ?_ }⟩
  · intro d
    exact (hUnit d).trans (comparison d)
  · intro d e g
    change old.map g ≫ inclusion theta L hNowQ e =
      inclusion theta L hPrev d ≫ (a.map g ≫ ((L e).map (hEQ e)).right)
    calc
      _ = (old.map g ≫ inclusion theta L hNowE e) ≫ ((L e).map (hEQ e)).right := by
        rw [Category.assoc, comparison]
      _ = _ := by simpa only [Over.mk_left, Over.mk_hom, Category.assoc] using hLadder e (Over.mk g)
  · intro d m e g k
    change old.map g ≫ (a.map k ≫ ((L e).map (hEQ e)).right) =
      old.map (g ≫ k) ≫ inclusion theta L hNowQ e
    calc
      _ = (old.map g ≫ a.map k) ≫ ((L e).map (hEQ e)).right :=
        (Category.assoc _ _ _).symm
      _ = (old.map (g ≫ k) ≫ inclusion theta L hNowE e) ≫ ((L e).map (hEQ e)).right :=
        hComp e ⟨Over.mk k, Over.mk g⟩
      _ = _ := by rw [Category.assoc, comparison]

/-- The exact original Nat refinement sequence, whose certificates are all outputs. -/
structure RefinementChain (chi : Cardinal.{w}) (seed : Supports (P := P) chi) where
  /-- The actual original supports at every natural stage. -/
  supports : ℕ → Supports (P := P) chi
  /-- Its original stage-zero support family is exactly the given seed. -/
  start : supports 0 = seed
  /-- Adjacent inclusions between these same supports. -/
  le (n : ℕ) (d : D) : supports n d ≤ supports (n + 1) d
  /-- The internally constructed original stage factors. -/
  factors (n : ℕ) : Factors theta L chi (supports n) (supports (n + 1))
  /-- Every stage unit is its actual selected comparison. -/
  unit (n : ℕ) (d : D) : (factors n).map (𝟙 d) = inclusion theta L (le n) d
  /-- The source and target ladder functions are the same original comparisons. -/
  ladder (n : ℕ) {d e : D} (g : d ⟶ e) :
    (factors n).map g ≫ inclusion theta L (le (n + 1)) e =
      inclusion theta L (le n) d ≫ (factors (n + 1)).map g
  /-- The original composition is delayed by exactly one target stage. -/
  composition (n : ℕ) {d m e : D} (g : d ⟶ m) (h : m ⟶ e) :
    (factors n).map g ≫ (factors (n + 1)).map h =
      (factors n).map (g ≫ h) ≫ inclusion theta L (le (n + 1)) e

/-- Internal state keeps its chosen source and target with both original factor laws. -/
structure State where
  /-- The actual original source supports of this internally chosen stage. -/
  source : Supports (P := P) chi
  /-- The same stage's actually chosen next original support family. -/
  target : Supports (P := P) chi
  le : ∀ d, source d ≤ target d
  /-- Every original arrow keeps its two actual root and endpoint equations. -/
  factors : Factors theta L chi source target
  unit (d : D) : factors.map (𝟙 d) = inclusion theta L le d

/-- The initial state has literally the supplied original source supports. -/
def initialState (seed : Supports (P := P) chi) : State theta L chi :=
  let S := Classical.choice (nonemptyUnitalStage theta L chi hArrow good seed)
  { source := seed, target := S.target, le := S.le, factors := S.factors, unit := S.unit }

/-- This single selected refinement value is shared by the successor and its certificates. -/
def refineState (S : State theta L chi) :
    RefinedStage theta L chi S.source S.target S.le S.factors :=
  Classical.choice (nonemptyRefinedStage theta L chi hArrow good S.source S.target S.le S.factors)

/-- The successor source is definitionally the preceding actual target support. -/
def nextState (S : State theta L chi) : State theta L chi :=
  let Q := refineState theta L chi hArrow good S
  { source := S.target, target := Q.target, le := Q.le, factors := Q.factors, unit := Q.unit }

/-- Ordinary Nat recursion constructs every original raw factor and equality certificate. -/
def states (seed : Supports (P := P) chi) : ℕ → State theta L chi :=
  Nat.rec (initialState theta L chi hArrow good seed)
    (fun _ S => nextState theta L chi hArrow good S)

/-- Construct a whole original refinement chain from primitive data and the original seeds. -/
def refinementChain (seed : Supports (P := P) chi) : RefinementChain theta L chi seed where
  supports n := (states theta L chi hArrow good seed n).source
  start := rfl
  le n := (states theta L chi hArrow good seed n).le
  factors n := (states theta L chi hArrow good seed n).factors
  unit n := (states theta L chi hArrow good seed n).unit
  ladder n := (refineState theta L chi hArrow good (states theta L chi hArrow good seed n)).ladder
  composition n :=
    (refineState theta L chi hArrow good (states theta L chi hArrow good seed n)).composition

end CategoryTheory.SmallObject.DiagramActionCapture
