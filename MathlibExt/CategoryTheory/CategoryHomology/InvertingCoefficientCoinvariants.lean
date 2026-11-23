/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.HomologyZeroColimit
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveUnit
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Conj
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Actual root actions of morphism-inverting coefficient functors

The existing fundamental-groupoid universal property extends a coefficient
functor which inverts its arrows. Its original restriction Iso gives the
actual root representation. Cocones extend by the existing natural-
transformation constructor, so their original root maps are invariant.

This is the universal-property construction used to compare coefficient
H₀ with actual root-action coinvariants. No action or root-coordinate
comparison is supplied as an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe uJ vJ uA

public section

namespace CategoryTheory.CategoryHomology

variable {J : Type uJ} [Category.{vJ} J] (M : J ⥤ AddCommGrpCat.{uA})
  [∀ {i j : J} (f : i ⟶ j), IsIso (M.map f)]

/-- The actual arrow-inverting coefficients extend through the existing fundamental groupoid. -/
def invertingCoefficientCore :
    SSet.FundamentalGroupoid (CategoryTheory.nerve J) ⥤ Core AddCommGrpCat.{uA} :=
  SSet.FundamentalGroupoid.desc
    (fun x : (CategoryTheory.nerve J) _⦋0⦌ => Core.mk (M.obj (CategoryTheory.nerveEquiv x)))
    (fun {x y : (CategoryTheory.nerve J) _⦋0⦌} e =>
      CoreHom.mk (asIso (M.map (CategoryTheory.nerve.homEquiv e))))
    (fun h => by
      apply Core.hom_ext
      exact (M.map_comp _ _).symm.trans
        (congrArg M.map (CategoryTheory.nerve.homEquiv_comp h)))

/-- The same computed extension valued in the original abelian-group category. -/
def invertingCoefficientExtension :
    SSet.FundamentalGroupoid (CategoryTheory.nerve J) ⥤ AddCommGrpCat.{uA} :=
  invertingCoefficientCore M ⋙ Core.inclusion AddCommGrpCat.{uA}

private theorem invertingCoefficientExtension_edge_raw
    {x y : (CategoryTheory.nerve J) _⦋0⦌} (e : (CategoryTheory.nerve J).Edge x y) :
    (invertingCoefficientExtension M).map (SSet.FundamentalGroupoid.homMk e) =
      M.map (CategoryTheory.nerve.homEquiv e) := by
  change ((invertingCoefficientCore M).map (SSet.FundamentalGroupoid.homMk e)).iso.hom = _
  have h := SSet.FundamentalGroupoid.desc_map_homMk
    (fun x : (CategoryTheory.nerve J) _⦋0⦌ => Core.mk (M.obj (CategoryTheory.nerveEquiv x)))
    (fun {x y : (CategoryTheory.nerve J) _⦋0⦌} e =>
      CoreHom.mk (asIso (M.map (CategoryTheory.nerve.homEquiv e))))
    (fun h => by
      apply Core.hom_ext
      exact (M.map_comp _ _).symm.trans
        (congrArg M.map (CategoryTheory.nerve.homEquiv_comp h))) e
  exact congrArg (fun f => f.iso.hom) h

/-- The extension recovers the original coefficients at the actual categorical unit. -/
def invertingCoefficientRestrictionIso :
    SSet.categoryNerveUnit J ⋙ invertingCoefficientExtension M ≅ M :=
  NatIso.ofComponents (fun j => Iso.refl (M.obj j)) (by
    intro i j f
    let F := invertingCoefficientExtension M
    let U := SSet.categoryNerveUnit J
    let x : (CategoryTheory.nerve J) _⦋0⦌ := CategoryTheory.nerveEquiv.symm i
    let y : (CategoryTheory.nerve J) _⦋0⦌ := CategoryTheory.nerveEquiv.symm j
    let ε : (CategoryTheory.nerve J).Edge x y := CategoryTheory.nerve.edgeMk f
    let u : U.obj i ⟶ U.obj j := U.map f
    let m : M.obj i ⟶ M.obj j := M.map f
    have hu : u = SSet.FundamentalGroupoid.homMk ε := SSet.categoryNerveUnit_map J f
    have hEdge : (F.map (SSet.FundamentalGroupoid.homMk ε) : M.obj i ⟶ M.obj j) = m :=
      (invertingCoefficientExtension_edge_raw M ε).trans
        (congrArg M.map (CategoryTheory.nerve.homEquiv_edgeMk f))
    have hMap : (F.map u : M.obj i ⟶ M.obj j) = m :=
      (congrArg F.map hu).trans hEdge
    change (F.map u : M.obj i ⟶ M.obj j) ≫ 𝟙 (M.obj j) = 𝟙 (M.obj i) ≫ m
    exact (Category.comp_id _).trans (hMap.trans (Category.id_comp m).symm))

/-- The computed extension object has its original coefficient coordinate. -/
def invertingCoefficientVertexIso (x : (CategoryTheory.nerve J) _⦋0⦌) :
    (invertingCoefficientExtension M).obj (SSet.FundamentalGroupoid.mk x) ≅
      M.obj (CategoryTheory.nerveEquiv x) := Iso.refl _

/-- The extension sends the original edge to its original coefficient map
in the computed endpoint coordinates. -/
theorem invertingCoefficientExtension_edge
    {x y : (CategoryTheory.nerve J) _⦋0⦌} (e : (CategoryTheory.nerve J).Edge x y) :
    (invertingCoefficientExtension M).map (SSet.FundamentalGroupoid.homMk e) ≫
        (invertingCoefficientVertexIso M y).hom =
      (invertingCoefficientVertexIso M x).hom ≫ M.map (CategoryTheory.nerve.homEquiv e) := by
  change (invertingCoefficientExtension M).map (SSet.FundamentalGroupoid.homMk e) ≫
      𝟙 (M.obj (CategoryTheory.nerveEquiv y)) =
    𝟙 (M.obj (CategoryTheory.nerveEquiv x)) ≫ M.map (CategoryTheory.nerve.homEquiv e)
  exact (Category.comp_id _).trans
    ((invertingCoefficientExtension_edge_raw M e).trans (Category.id_comp _).symm)

private def additiveEndToIntLinear (V : AddCommGrpCat.{uA}) :
    End V →* Module.End ℤ V where
  toFun g := g.asHom.hom.toIntLinearMap
  map_one' := by ext v; rfl
  map_mul' g h := by ext v; rfl

/-- The actual coefficient root action, with its computed original restriction coordinate. -/
def invertingCoefficientRootAction (i : J) :
    Representation ℤ (End ((SSet.categoryNerveUnit J).obj i)) (M.obj i) :=
  (additiveEndToIntLinear (M.obj i)).comp
    (((invertingCoefficientRestrictionIso M).app i).conj.toMonoidHom.comp
      ((invertingCoefficientExtension M).mapEnd ((SSet.categoryNerveUnit J).obj i)))

/-- The root-action value is the original mapped endomorphism in its computed restriction
coordinate. -/
theorem invertingCoefficientRootAction_apply (i : J)
    (g : End ((SSet.categoryNerveUnit J).obj i)) (v : M.obj i) :
    invertingCoefficientRootAction M i g v =
      (((invertingCoefficientRestrictionIso M).app i).inv ≫
        (invertingCoefficientExtension M).map g.asHom ≫
          ((invertingCoefficientRestrictionIso M).app i).hom).hom v := by
  unfold invertingCoefficientRootAction additiveEndToIntLinear
  rfl

private def invertingCoefficientCoconeExtension (s : Cocone M) :
    invertingCoefficientExtension M ⟶
      (Functor.const (SSet.FundamentalGroupoid (CategoryTheory.nerve J))).obj s.pt :=
  SSet.FundamentalGroupoid.natTransMk
    (fun x : (CategoryTheory.nerve J) _⦋0⦌ => s.ι.app (CategoryTheory.nerveEquiv x))
    (fun {x y} e => by
      rw [invertingCoefficientExtension_edge_raw]
      change M.map (CategoryTheory.nerve.homEquiv e) ≫
          s.ι.app (CategoryTheory.nerveEquiv y) =
        s.ι.app (CategoryTheory.nerveEquiv x) ≫ 𝟙 _
      exact (s.w (CategoryTheory.nerve.homEquiv e)).trans (Category.comp_id _).symm)

private theorem invertingCoefficientCoconeExtension_app (s : Cocone M) (i : J) :
    (invertingCoefficientCoconeExtension M s).app ((SSet.categoryNerveUnit J).obj i) =
      ((invertingCoefficientRestrictionIso M).app i).hom ≫ s.ι.app i := by
  change s.ι.app i = 𝟙 (M.obj i) ≫ s.ι.app i
  exact (Category.id_comp _).symm

/-- Every original cocone map is invariant under the derived actual root action. -/
theorem invertingCoefficientRootAction_cocone_invariant (s : Cocone M) (i : J)
    (g : End ((SSet.categoryNerveUnit J).obj i)) :
    (s.ι.app i).hom.toIntLinearMap ∘ₗ invertingCoefficientRootAction M i g =
      (s.ι.app i).hom.toIntLinearMap := by
  let F := invertingCoefficientExtension M
  let e := (invertingCoefficientRestrictionIso M).app i
  let τ := invertingCoefficientCoconeExtension M s
  have h := τ.naturality g.asHom
  rw [invertingCoefficientCoconeExtension_app] at h
  change F.map g.asHom ≫ (e.hom ≫ s.ι.app i) = (e.hom ≫ s.ι.app i) ≫ 𝟙 _ at h
  have hInv : (e.inv ≫ F.map g.asHom ≫ e.hom) ≫ s.ι.app i = s.ι.app i := by
    have t := congrArg (fun k => e.inv ≫ k) h
    simpa only [Category.assoc, Category.comp_id, e.inv_hom_id_assoc] using t
  apply LinearMap.ext
  intro v
  change (s.ι.app i).hom (invertingCoefficientRootAction M i g v) = (s.ι.app i).hom v
  rw [invertingCoefficientRootAction_apply]
  exact ConcreteCategory.congr_hom hInv v

section NaturalMaps

variable {N : J ⥤ AddCommGrpCat.{uA}}
  [∀ {i j : J} (f : i ⟶ j), IsIso (N.map f)]

/-- The original coefficient natural transformation extends through the same groupoid. -/
def invertingCoefficientExtensionMap (α : M ⟶ N) :
    invertingCoefficientExtension M ⟶ invertingCoefficientExtension N :=
  SSet.FundamentalGroupoid.natTransMk
    (fun x : (CategoryTheory.nerve J) _⦋0⦌ => α.app (CategoryTheory.nerveEquiv x))
    (fun {x y} e => by
      rw [invertingCoefficientExtension_edge_raw, invertingCoefficientExtension_edge_raw]
      exact α.naturality (CategoryTheory.nerve.homEquiv e))

/-- The original component is retained through the SAME computed restriction coordinates. -/
theorem invertingCoefficientExtensionMap_app (α : M ⟶ N) (i : J) :
    (invertingCoefficientExtensionMap M α).app ((SSet.categoryNerveUnit J).obj i) ≫
        ((invertingCoefficientRestrictionIso N).app i).hom =
      ((invertingCoefficientRestrictionIso M).app i).hom ≫ α.app i := by
  change α.app i ≫ 𝟙 (N.obj i) = 𝟙 (M.obj i) ≫ α.app i
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Every original coefficient map intertwines the two computed actual root actions. -/
def invertingCoefficientRootMap (α : M ⟶ N) (i : J) :
    Representation.IntertwiningMap (invertingCoefficientRootAction M i)
      (invertingCoefficientRootAction N i) where
  toLinearMap := (α.app i).hom.toIntLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let a : M.obj i ⟶ N.obj i := α.app i
    let FM := invertingCoefficientExtension M
    let FN := invertingCoefficientExtension N
    let eM := (invertingCoefficientRestrictionIso M).app i
    let eN := (invertingCoefficientRestrictionIso N).app i
    let s := FM.map g.asHom
    let t := FN.map g.asHom
    let b := (invertingCoefficientExtensionMap M α).app ((SSet.categoryNerveUnit J).obj i)
    have hNat : s ≫ b = b ≫ t := (invertingCoefficientExtensionMap M α).naturality g.asHom
    have hRestriction : b ≫ eN.hom = eM.hom ≫ a := invertingCoefficientExtensionMap_app M α i
    have hBack : a ≫ eN.inv = eM.inv ≫ b := by
      apply (cancel_mono eN.hom).mp
      have hL : (a ≫ eN.inv) ≫ eN.hom = a :=
        (Category.assoc a eN.inv eN.hom).trans
          ((congrArg (fun k => a ≫ k) eN.inv_hom_id).trans (Category.comp_id a))
      have hR : (eM.inv ≫ b) ≫ eN.hom = a :=
        (Category.assoc eM.inv b eN.hom).trans
          ((congrArg (fun k => eM.inv ≫ k) hRestriction).trans
            ((Category.assoc eM.inv eM.hom a).symm.trans
              ((congrArg (fun k => k ≫ a) eM.inv_hom_id).trans (Category.id_comp a))))
      exact hL.trans hR.symm
    have hSquare : (eM.inv ≫ s ≫ eM.hom) ≫ a = a ≫ eN.inv ≫ t ≫ eN.hom :=
      (Category.assoc eM.inv (s ≫ eM.hom) a).trans
        ((congrArg (fun k => eM.inv ≫ k) (Category.assoc s eM.hom a)).trans
          ((congrArg (fun k => eM.inv ≫ (s ≫ k)) hRestriction.symm).trans
            ((congrArg (fun k => eM.inv ≫ k) (Category.assoc s b eN.hom).symm).trans
              ((congrArg (fun k => eM.inv ≫ (k ≫ eN.hom)) hNat).trans
                ((congrArg (fun k => eM.inv ≫ k) (Category.assoc b t eN.hom)).trans
                  ((Category.assoc eM.inv b (t ≫ eN.hom)).symm.trans
                    ((congrArg (fun k => k ≫ (t ≫ eN.hom)) hBack.symm).trans
                      (Category.assoc a eN.inv (t ≫ eN.hom)))))))))
    have hValue : a.hom ((eM.inv ≫ s ≫ eM.hom).hom v) =
        (eN.inv ≫ t ≫ eN.hom).hom (a.hom v) := ConcreteCategory.congr_hom hSquare v
    have hM : invertingCoefficientRootAction M i g v = (eM.inv ≫ s ≫ eM.hom).hom v :=
      invertingCoefficientRootAction_apply M i g v
    have hN : invertingCoefficientRootAction N i g (a.hom v) =
        (eN.inv ≫ t ≫ eN.hom).hom (a.hom v) :=
      invertingCoefficientRootAction_apply N i g (a.hom v)
    exact (congrArg a.hom hM).trans (hValue.trans hN.symm)

/-- The intertwining map's value is precisely the original coefficient map. -/
theorem invertingCoefficientRootMap_apply (α : M ⟶ N) (i : J) (v : M.obj i) :
    invertingCoefficientRootMap M α i v = (α.app i).hom v := by
  change (α.app i).hom.toIntLinearMap v = (α.app i).hom v
  rfl

end NaturalMaps

section Connected

variable [(CategoryTheory.nerve J).IsConnected]

private theorem coefficientPath_nonempty (i j : J) :
    Nonempty ((SSet.categoryNerveUnit J).obj i ⟶ (SSet.categoryNerveUnit J).obj j) := by
  let x : (CategoryTheory.nerve J) _⦋0⦌ := CategoryTheory.nerveEquiv.symm i
  let y : (CategoryTheory.nerve J) _⦋0⦌ := CategoryTheory.nerveEquiv.symm j
  have h : SSet.π₀.mk x = SSet.π₀.mk y := Subsingleton.elim _ _
  have hHom : ∀ {a b : (CategoryTheory.nerve J) _⦋0⦌},
      Relation.EqvGen SSet.π₀Rel a b →
        Nonempty (SSet.FundamentalGroupoid.mk a ⟶ SSet.FundamentalGroupoid.mk b) := by
    intro a b hab
    induction hab with
    | rel _ _ h => exact ⟨SSet.FundamentalGroupoid.homMk h.some⟩
    | refl => exact ⟨𝟙 _⟩
    | symm _ _ _ ih => exact ⟨inv ih.some⟩
    | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some ≫ ih₂.some⟩
  rw [SSet.π₀.mk_eq_mk_iff] at h
  change Nonempty (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk y)
  exact hHom h

private def coefficientReferencePath (i j : J) :
    (SSet.categoryNerveUnit J).obj i ⟶ (SSet.categoryNerveUnit J).obj j := by
  classical
  exact if h : j = i then eqToHom (congrArg (SSet.categoryNerveUnit J).obj h.symm)
    else (coefficientPath_nonempty i j).some

private theorem coefficientReferencePath_self (i : J) :
    coefficientReferencePath i i = 𝟙 _ := by
  classical
  simp only [coefficientReferencePath, dite_eq_left rfl, eqToHom_refl]

/-- Transport through the actual chosen path back to the original coefficient root. -/
def invertingCoefficientRootTransport (i j : J) : M.obj j ⟶ M.obj i :=
  ((invertingCoefficientRestrictionIso M).app j).inv ≫
    (invertingCoefficientExtension M).map (inv (coefficientReferencePath i j)) ≫
      ((invertingCoefficientRestrictionIso M).app i).hom

/-- The root path is computed to be identity; no root-coordinate witness is given. -/
theorem invertingCoefficientRootTransport_self (i : J) :
    invertingCoefficientRootTransport M i i = 𝟙 _ := by
  let e := (invertingCoefficientRestrictionIso M).app i
  change e.inv ≫
    (invertingCoefficientExtension M).map (inv (coefficientReferencePath i i)) ≫ e.hom = 𝟙 _
  let F := invertingCoefficientExtension M
  let g := inv (coefficientReferencePath i i)
  have hg : g = 𝟙 ((SSet.categoryNerveUnit J).obj i) :=
    (congrArg (fun k => inv k) (coefficientReferencePath_self i)).trans IsIso.inv_id
  have hm : F.map g = 𝟙 (F.obj ((SSet.categoryNerveUnit J).obj i)) :=
    (congrArg F.map hg).trans (F.map_id _)
  change e.inv ≫ (F.map g ≫ e.hom) = 𝟙 (M.obj i)
  exact (congrArg (fun k => e.inv ≫ (k ≫ e.hom)) hm).trans
    ((congrArg (fun k => e.inv ≫ k) (Category.id_comp e.hom)).trans e.inv_hom_id)

private def rootActionHom (i : J) (g : End ((SSet.categoryNerveUnit J).obj i)) :
    M.obj i ⟶ M.obj i :=
  AddCommGrpCat.ofHom (invertingCoefficientRootAction M i g).toAddMonoidHom

omit [(CategoryTheory.nerve J).IsConnected] in
private theorem rootActionHom_eq (i : J) (g : End ((SSet.categoryNerveUnit J).obj i)) :
    rootActionHom M i g = ((invertingCoefficientRestrictionIso M).app i).inv ≫
      (invertingCoefficientExtension M).map g.asHom ≫
        ((invertingCoefficientRestrictionIso M).app i).hom := rfl

private theorem rootTransport_arrow (i : J) {j k : J} (f : j ⟶ k) :
    M.map f ≫ invertingCoefficientRootTransport M i k =
      invertingCoefficientRootTransport M i j ≫ rootActionHom M i
        (End.of (coefficientReferencePath i j ≫ (SSet.categoryNerveUnit J).map f ≫
          inv (coefficientReferencePath i k))) := by
  let F := invertingCoefficientExtension M
  let e := invertingCoefficientRestrictionIso M
  let l := coefficientReferencePath i j
  let r := coefficientReferencePath i k
  let u := (SSet.categoryNerveUnit J).map f
  have hNat : M.map f ≫ (e.app k).inv = (e.app j).inv ≫ F.map u :=
    e.inv.naturality f
  have hLoop : inv l ≫ (l ≫ u ≫ inv r) = u ≫ inv r :=
    (Category.assoc (inv l) l (u ≫ inv r)).symm.trans
      ((congrArg (fun k => k ≫ (u ≫ inv r)) (IsIso.inv_hom_id l)).trans
        (Category.id_comp _))
  have hMap : F.map (inv l) ≫ F.map (l ≫ u ≫ inv r) = F.map u ≫ F.map (inv r) :=
    (F.map_comp _ _).symm.trans ((congrArg F.map hLoop).trans (F.map_comp _ _))
  let a := (e.app j).inv
  let b := F.map (inv l)
  let c := F.map (l ≫ u ≫ inv r) ≫ (e.app i).hom
  let ei := e.app i
  have hCancel : ei.hom ≫ (ei.inv ≫ c) = c :=
    (Category.assoc ei.hom ei.inv c).symm.trans
      ((congrArg (fun k => k ≫ c) ei.hom_inv_id).trans (Category.id_comp c))
  have hRight : (a ≫ b ≫ ei.hom) ≫ (ei.inv ≫ c) = a ≫ b ≫ c :=
    (congrArg (fun k => k ≫ (ei.inv ≫ c)) (Category.assoc a b ei.hom).symm).trans
      ((Category.assoc (a ≫ b) ei.hom (ei.inv ≫ c)).trans
        ((congrArg (fun k => (a ≫ b) ≫ k) hCancel).trans (Category.assoc a b c)))
  have hLeft : M.map f ≫ ((e.app k).inv ≫ F.map (inv r) ≫ ei.hom) =
      a ≫ b ≫ c :=
    (Category.assoc (M.map f) (e.app k).inv (F.map (inv r) ≫ ei.hom)).symm.trans
      ((congrArg (fun q => q ≫ (F.map (inv r) ≫ ei.hom)) hNat).trans
        ((Category.assoc a (F.map u) (F.map (inv r) ≫ ei.hom)).trans
          ((congrArg (fun q => a ≫ q) (Category.assoc (F.map u) (F.map (inv r)) ei.hom).symm).trans
            ((congrArg (fun q => a ≫ (q ≫ ei.hom)) hMap.symm).trans
              (congrArg (fun q => a ≫ q) (Category.assoc b (F.map (l ≫ u ≫ inv r)) ei.hom))))))
  rw [rootActionHom_eq]
  change M.map f ≫ ((e.app k).inv ≫ F.map (inv r) ≫ ei.hom) =
    (a ≫ b ≫ ei.hom) ≫ (ei.inv ≫ c)
  exact hLeft.trans hRight.symm

private def rootCoinvariantProjection (i : J) :
    M.obj i ⟶ AddCommGrpCat.of (Representation.Coinvariants (invertingCoefficientRootAction M i)) :=
  AddCommGrpCat.ofHom (Representation.Coinvariants.mk
      (invertingCoefficientRootAction M i)).toAddMonoidHom

omit [(CategoryTheory.nerve J).IsConnected] in
private theorem rootCoinvariantProjection_action (i : J)
    (g : End ((SSet.categoryNerveUnit J).obj i)) :
    rootActionHom M i g ≫ rootCoinvariantProjection M i = rootCoinvariantProjection M i := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro v
  exact Representation.Coinvariants.mk_self_apply (invertingCoefficientRootAction M i) g v

private def rootCoinvariantCocone (i : J) : Cocone M where
  pt := AddCommGrpCat.of (Representation.Coinvariants (invertingCoefficientRootAction M i))
  ι :=
    { app := fun j => invertingCoefficientRootTransport M i j ≫ rootCoinvariantProjection M i
      naturality := fun {j k} f => by
        change M.map f ≫ (invertingCoefficientRootTransport M i k ≫
          rootCoinvariantProjection M i) =
          (invertingCoefficientRootTransport M i j ≫ rootCoinvariantProjection M i) ≫ 𝟙 _
        rw [← Category.assoc, rootTransport_arrow, Category.assoc,
          rootCoinvariantProjection_action, Category.comp_id] }

/-- The original transport carries every cocone value to the value at the original object. -/
theorem invertingCoefficientRootTransport_comp_cocone (s : Cocone M) (i j : J) :
    invertingCoefficientRootTransport M i j ≫ s.ι.app i = s.ι.app j := by
  let F := invertingCoefficientExtension M
  let e := invertingCoefficientRestrictionIso M
  let r := coefficientReferencePath i j
  let τ := invertingCoefficientCoconeExtension M s
  let ji : M.obj i ⟶ s.pt := s.ι.app i
  let jj : M.obj j ⟶ s.pt := s.ι.app j
  let ti : F.obj ((SSet.categoryNerveUnit J).obj i) ⟶ s.pt :=
    τ.app ((SSet.categoryNerveUnit J).obj i)
  let tj : F.obj ((SSet.categoryNerveUnit J).obj j) ⟶ s.pt :=
    τ.app ((SSet.categoryNerveUnit J).obj j)
  let m : s.pt ⟶ s.pt :=
    ((Functor.const (SSet.FundamentalGroupoid (CategoryTheory.nerve J))).obj s.pt).map (inv r)
  have hNat : F.map (inv r) ≫ ti = tj ≫ m := τ.naturality (inv r)
  have hi : ti = (e.app i).hom ≫ ji := invertingCoefficientCoconeExtension_app M s i
  have hj : tj = (e.app j).hom ≫ jj := invertingCoefficientCoconeExtension_app M s j
  have hId : m = 𝟙 s.pt := rfl
  have hTyped : F.map (inv r) ≫ ((e.app i).hom ≫ ji) = (e.app j).hom ≫ jj :=
    (congrArg (fun k => F.map (inv r) ≫ k) hi.symm).trans
      (hNat.trans
        ((congrArg₂ (fun a b => a ≫ b) hj hId).trans (Category.comp_id _)))
  change ((e.app j).inv ≫ F.map (inv r) ≫ (e.app i).hom) ≫ ji = jj
  exact (Category.assoc (e.app j).inv (F.map (inv r) ≫ (e.app i).hom) ji).trans
    ((congrArg (fun k => (e.app j).inv ≫ k) (Category.assoc (F.map (inv r)) (e.app i).hom ji)).trans
      ((congrArg (fun k => (e.app j).inv ≫ k) hTyped).trans
        ((Category.assoc (e.app j).inv (e.app j).hom jj).symm.trans
          ((congrArg (fun k => k ≫ jj) (e.app j).inv_hom_id).trans (Category.id_comp jj)))))

variable [HasColimit M]

private def colimitToRootCoinvariants (i : J) :
    colimit M ⟶
        AddCommGrpCat.of (Representation.Coinvariants (invertingCoefficientRootAction M i)) :=
  colimit.desc M (rootCoinvariantCocone M i)

private def rootCoinvariantsToColimit (i : J) :
    AddCommGrpCat.of (Representation.Coinvariants (invertingCoefficientRootAction M i)) ⟶
        colimit M :=
  AddCommGrpCat.ofHom
    (Representation.Coinvariants.lift (invertingCoefficientRootAction M i)
      (colimit.ι M i).hom.toIntLinearMap
      (fun g => invertingCoefficientRootAction_cocone_invariant M
          (colimit.cocone M) i g)).toAddMonoidHom

private theorem colimitToRootCoinvariants_class (i j : J) :
    colimit.ι M j ≫ colimitToRootCoinvariants M i =
      invertingCoefficientRootTransport M i j ≫ rootCoinvariantProjection M i :=
  colimit.ι_desc (rootCoinvariantCocone M i) j

omit [(CategoryTheory.nerve J).IsConnected] in
private theorem rootCoinvariantsToColimit_projection (i : J) :
    rootCoinvariantProjection M i ≫ rootCoinvariantsToColimit M i = colimit.ι M i := by
  apply AddCommGrpCat.hom_ext
  exact congrArg LinearMap.toAddMonoidHom
    (Representation.Coinvariants.lift_comp_mk (invertingCoefficientRootAction M i)
      (colimit.ι M i).hom.toIntLinearMap
      (fun g => invertingCoefficientRootAction_cocone_invariant M (colimit.cocone M) i g))

/-- The actual coefficient colimit is the actual coinvariant quotient of its computed root
action. -/
def invertingCoefficientColimitCoinvariantsIso (i : J) :
    colimit M ≅ AddCommGrpCat.of
      (Representation.Coinvariants (invertingCoefficientRootAction M i)) where
  hom := colimitToRootCoinvariants M i
  inv := rootCoinvariantsToColimit M i
  hom_inv_id := by
    apply colimit.hom_ext
    intro j
    let p := colimitToRootCoinvariants M i
    let q := rootCoinvariantsToColimit M i
    let t := invertingCoefficientRootTransport M i j
    let r := rootCoinvariantProjection M i
    have hP : colimit.ι M j ≫ p = t ≫ r := colimitToRootCoinvariants_class M i j
    have hQ : r ≫ q = colimit.ι M i := rootCoinvariantsToColimit_projection M i
    have hReturn : t ≫ colimit.ι M i = colimit.ι M j :=
      invertingCoefficientRootTransport_comp_cocone M (colimit.cocone M) i j
    change colimit.ι M j ≫ (p ≫ q) = colimit.ι M j ≫ 𝟙 _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ q) hP).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => t ≫ k) hQ).trans (hReturn.trans (Category.comp_id _).symm))))
  inv_hom_id := by
    let p := colimitToRootCoinvariants M i
    let q := rootCoinvariantsToColimit M i
    let rho := invertingCoefficientRootAction M i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro v
    change p.hom (q.hom v) = v
    refine Representation.Coinvariants.induction_on
      (motive := fun v : Representation.Coinvariants rho => p.hom (q.hom v) = v) v ?_
    intro a
    have hInv : q.hom (Representation.Coinvariants.mk rho a) = (colimit.ι M i).hom a :=
      ConcreteCategory.congr_hom (rootCoinvariantsToColimit_projection M i) a
    have hRoot : colimit.ι M i ≫ p = rootCoinvariantProjection M i :=
      (colimitToRootCoinvariants_class M i i).trans
        ((congrArg (fun k => k ≫ rootCoinvariantProjection M i)
          (invertingCoefficientRootTransport_self M i)).trans (Category.id_comp _))
    have hForward : p.hom ((colimit.ι M i).hom a) = Representation.Coinvariants.mk rho a :=
      ConcreteCategory.congr_hom hRoot a
    exact (congrArg p.hom hInv).trans hForward

/-- Every original object class is transported to the actual root coinvariant quotient. -/
theorem invertingCoefficientColimitCoinvariantsIso_class (i j : J) :
    colimit.ι M j ≫ (invertingCoefficientColimitCoinvariantsIso M i).hom =
      invertingCoefficientRootTransport M i j ≫
        AddCommGrpCat.ofHom
          (Representation.Coinvariants.mk (invertingCoefficientRootAction M i)).toAddMonoidHom := by
  change colimit.ι M j ≫ colimitToRootCoinvariants M i =
    invertingCoefficientRootTransport M i j ≫ rootCoinvariantProjection M i
  exact colimitToRootCoinvariants_class M i j

/-- The actual original coefficient H₀ is the computed root-action coinvariants. -/
def invertingCoefficientHomologyZeroCoinvariantsIso
    [HasCoproducts.{max uJ vJ} AddCommGrpCat.{uA}] (i : J) :
    homologyWithCoefficients M 0 ≅ AddCommGrpCat.of
      (Representation.Coinvariants (invertingCoefficientRootAction M i)) :=
  coefficientHomologyZeroColimitIso M ≪≫ invertingCoefficientColimitCoinvariantsIso M i

/-- The original root class is sent to the ACTUAL coinvariant quotient projection. -/
theorem invertingCoefficientHomologyZeroCoinvariantsIso_class
    [HasCoproducts.{max uJ vJ} AddCommGrpCat.{uA}] (i : J) :
    coefficientHomologyClass M i ≫ (invertingCoefficientHomologyZeroCoinvariantsIso M i).hom =
      AddCommGrpCat.ofHom
        (Representation.Coinvariants.mk (invertingCoefficientRootAction M i)).toAddMonoidHom := by
  change coefficientHomologyClass M i ≫
      ((coefficientHomologyZeroColimitIso M).hom ≫ colimitToRootCoinvariants M i) = _
  rw [← Category.assoc, coefficientHomologyZeroColimitIso_class,
    colimitToRootCoinvariants_class, invertingCoefficientRootTransport_self, Category.id_comp]
  rfl

/-- Every original H₀ object class retains its computed transport to the root quotient. -/
theorem invertingCoefficientHomologyZeroCoinvariantsIso_object_class
    [HasCoproducts.{max uJ vJ} AddCommGrpCat.{uA}] (i j : J) :
    coefficientHomologyClass M j ≫ (invertingCoefficientHomologyZeroCoinvariantsIso M i).hom =
      invertingCoefficientRootTransport M i j ≫
        AddCommGrpCat.ofHom
          (Representation.Coinvariants.mk (invertingCoefficientRootAction M i)).toAddMonoidHom := by
  let a := coefficientHomologyClass M j
  let e := (coefficientHomologyZeroColimitIso M).hom
  let b := (invertingCoefficientColimitCoinvariantsIso M i).hom
  have h : a ≫ e = colimit.ι M j := coefficientHomologyZeroColimitIso_class M j
  change a ≫ (e ≫ b) = _
  exact (Category.assoc a e b).symm.trans
    ((congrArg (fun k => k ≫ b) h).trans
      (invertingCoefficientColimitCoinvariantsIso_class M i j))

/-- Vanishing of the actual coefficient H₀ makes the computed root-action
coinvariants zero, using the derived comparison rather than a supplied Iso. -/
theorem invertingCoefficientCoinvariants_subsingleton_of_homologyZero_isZero
    [HasCoproducts.{max uJ vJ} AddCommGrpCat.{uA}] (i : J)
    (h : IsZero (homologyWithCoefficients M 0)) :
    Subsingleton (Representation.Coinvariants (invertingCoefficientRootAction M i)) := by
  let V := AddCommGrpCat.of
    (Representation.Coinvariants (invertingCoefficientRootAction M i))
  have hz : IsZero V := IsZero.of_iso h
    (invertingCoefficientHomologyZeroCoinvariantsIso M i).symm
  have he : (𝟙 V) = 0 := (IsZero.iff_id_eq_zero V).mp hz
  constructor
  intro a b
  exact (ConcreteCategory.congr_hom he a).trans (ConcreteCategory.congr_hom he b).symm

end Connected

end CategoryTheory.CategoryHomology

end
