/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverPullbackCopies
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Logic.Equiv.Prod

/-!
# Copies of map families in a native cover

For a Kan simplicial set with a chosen vertex and an identification of its
fundamental group with a group, decomposes the pullback of a coproduct of maps
into copies indexed by that group and the original family. Computes both
projection legs and their compatibility with deck transformations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace SSet.KanComplex

variable {Y V : SSet.{u}} {y : Y _⦋0⦌} [Y.KanComplex]
variable {G I : Type u} [Group G]

/-- The whole family lift, with each original selected first-path coordinate retained. -/
def nativeCoverCellFamilyLift (l : I → (V ⟶ nativeCover Y y)) :
    (∐ fun _ : I => V) ⟶ nativeCover Y y :=
  CategoryTheory.Limits.Sigma.desc l

omit [Y.KanComplex] in
/-- Every injection in the whole family is its same originally chosen lift. -/
theorem nativeCoverCellFamilyLift_ι (l : I → (V ⟶ nativeCover Y y)) (i : I) :
    CategoryTheory.Limits.Sigma.ι (fun _ : I => V) i ≫ nativeCoverCellFamilyLift l = l i := by
  exact CategoryTheory.Limits.Sigma.ι_comp_desc l i

/-- A labelled cell uses the same selected lift followed by its actual deck map. -/
def nativeCoverCellCopy (l : I → (V ⟶ nativeCover Y y))
    (e : G ≃* End (SSet.FundamentalGroupoid.mk y)) (i : G × I) :
    V ⟶ pullback (nativeCoverCellFamilyLift l ≫ nativeCoverProjection Y y)
      (nativeCoverProjection Y y) :=
  CategoryTheory.Limits.Sigma.ι (fun _ : I => V) i.2 ≫
    nativeCoverCopyLift (nativeCoverCellFamilyLift l) (e i.1)

omit [Y.KanComplex] in
/-- Its first projection is the original cell-family injection. -/
theorem nativeCoverCellCopy_fst (l : I → (V ⟶ nativeCover Y y))
    (e : G ≃* End (SSet.FundamentalGroupoid.mk y)) (i : G × I) :
    nativeCoverCellCopy l e i ≫
      pullback.fst (nativeCoverCellFamilyLift l ≫ nativeCoverProjection Y y)
        (nativeCoverProjection Y y) = CategoryTheory.Limits.Sigma.ι (fun _ : I => V) i.2 :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => CategoryTheory.Limits.Sigma.ι (fun _ : I => V) i.2 ≫ k)
      (nativeCoverCopyLift_fst (nativeCoverCellFamilyLift l) (e i.1))).trans
        (Category.comp_id _))

omit [Y.KanComplex] in
/-- Its second projection is the whole chosen lift and actual deck translate. -/
theorem nativeCoverCellCopy_snd (l : I → (V ⟶ nativeCover Y y))
    (e : G ≃* End (SSet.FundamentalGroupoid.mk y)) (i : G × I) :
    nativeCoverCellCopy l e i ≫
      pullback.snd (nativeCoverCellFamilyLift l ≫ nativeCoverProjection Y y)
        (nativeCoverProjection Y y) = l i.2 ≫ nativeCoverDeckMap (e i.1) := by
  let a := CategoryTheory.Limits.Sigma.ι (fun _ : I => V) i.2
  let L := nativeCoverCellFamilyLift l
  let d := nativeCoverDeckMap (e i.1)
  have hL : a ≫ L = l i.2 := CategoryTheory.Limits.Sigma.ι_comp_desc l i.2
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => a ≫ k) (nativeCoverCopyLift_snd L (e i.1))).trans
      ((Category.assoc a L d).symm.trans (congrArg (fun k => k ≫ d) hL)))

/-- Every group label and every original cell form the entire literal pulled
cell family. This is the existing native-copy Iso with stock coproduct reindexing. -/
def nativeCoverCellFamilyCopiesIso (l : I → (V ⟶ nativeCover Y y))
    (e : G ≃* End (SSet.FundamentalGroupoid.mk y)) :
    (∐ fun _ : G × I => V) ≅
      pullback (nativeCoverCellFamilyLift l ≫ nativeCoverProjection Y y)
        (nativeCoverProjection Y y) := by
  let a : (∐ fun _ : G × I => V) ≅ (∐ fun _ : Σ _ : G, I => V) :=
    CategoryTheory.Limits.Sigma.reindex (Equiv.sigmaEquivProd G I).symm (fun _ => V)
  let b : (∐ fun _ : Σ _ : G, I => V) ≅ (∐ fun _ : G => (∐ fun _ : I => V)) :=
    (CategoryTheory.Limits.sigmaSigmaIso (fun _ : G => I) (fun _ _ => V)).symm
  let c : (∐ fun _ : G => (∐ fun _ : I => V)) ≅
      (∐ fun _ : End (SSet.FundamentalGroupoid.mk y) => (∐ fun _ : I => V)) :=
    CategoryTheory.Limits.Sigma.reindex e.toEquiv (fun _ => (∐ fun _ : I => V))
  exact a ≪≫ b ≪≫ c ≪≫ nativeCoverPullbackCopiesIso (nativeCoverCellFamilyLift l)

/-- The complete family Iso sends each injection to the same actual labelled cell. -/
theorem nativeCoverCellFamilyCopiesIso_ι (l : I → (V ⟶ nativeCover Y y))
    (e : G ≃* End (SSet.FundamentalGroupoid.mk y)) (i : G × I) :
    CategoryTheory.Limits.Sigma.ι (fun _ : G × I => V) i ≫
        (nativeCoverCellFamilyCopiesIso l e).hom = nativeCoverCellCopy l e i := by
  rcases i with ⟨q,p⟩
  let a : (∐ fun _ : G × I => V) ≅ (∐ fun _ : Σ _ : G, I => V) :=
    CategoryTheory.Limits.Sigma.reindex (Equiv.sigmaEquivProd G I).symm (fun _ => V)
  let b : (∐ fun _ : Σ _ : G, I => V) ≅ (∐ fun _ : G => (∐ fun _ : I => V)) :=
    (CategoryTheory.Limits.sigmaSigmaIso (fun _ : G => I) (fun _ _ => V)).symm
  let c : (∐ fun _ : G => (∐ fun _ : I => V)) ≅
      (∐ fun _ : End (SSet.FundamentalGroupoid.mk y) => (∐ fun _ : I => V)) :=
    CategoryTheory.Limits.Sigma.reindex e.toEquiv (fun _ => (∐ fun _ : I => V))
  let L := nativeCoverCellFamilyLift l
  let z := nativeCoverPullbackCopiesIso L
  let j : V ⟶ (∐ fun _ : G × I => V) :=
    CategoryTheory.Limits.Sigma.ι (fun _ : G × I => V) (q,p)
  let k : V ⟶ (∐ fun _ : Σ _ : G, I => V) :=
    CategoryTheory.Limits.Sigma.ι (fun _ : Σ _ : G, I => V) ⟨q,p⟩
  let r : V ⟶ (∐ fun _ : I => V) := CategoryTheory.Limits.Sigma.ι (fun _ : I => V) p
  let t : (∐ fun _ : I => V) ⟶ (∐ fun _ : G => (∐ fun _ : I => V)) :=
    CategoryTheory.Limits.Sigma.ι (fun _ : G => (∐ fun _ : I => V)) q
  let w : (∐ fun _ : I => V) ⟶
      (∐ fun _ : End (SSet.FundamentalGroupoid.mk y) => (∐ fun _ : I => V)) :=
    CategoryTheory.Limits.Sigma.ι
      (fun _ : End (SSet.FundamentalGroupoid.mk y) => (∐ fun _ : I => V)) (e q)
  have hA : j ≫ a.hom = k := by
    let ε : (G × I) ≃ (Σ _ : G, I) := (Equiv.sigmaEquivProd G I).symm
    let fA : (Σ _ : G, I) → SSet.{u} := fun _ => V
    let fB : (G × I) → SSet.{u} := fA ∘ ε
    have hStock : CategoryTheory.Limits.Sigma.ι fB (q,p) ≫
        (CategoryTheory.Limits.Sigma.reindex ε fA).hom =
          CategoryTheory.Limits.Sigma.ι fA (ε (q,p)) :=
      CategoryTheory.Limits.Sigma.ι_reindex_hom ε fA (q,p)
    have hj : j = (CategoryTheory.Limits.Sigma.ι fB (q,p) : V ⟶ (∐ fB)) := rfl
    have ha : a.hom = (CategoryTheory.Limits.Sigma.reindex ε fA).hom := rfl
    have hk : k = (CategoryTheory.Limits.Sigma.ι fA (ε (q,p)) : V ⟶ (∐ fA)) := rfl
    exact (congrArg₂ (fun (s : V ⟶ (∐ fB)) (t : (∐ fB) ⟶ (∐ fA)) => s ≫ t)
      hj ha).trans (hStock.trans hk.symm)
  have hB : k ≫ b.hom = r ≫ t := by
    dsimp only [k, b, r, t, Iso.symm_hom, CategoryTheory.Limits.sigmaSigmaIso]
    simp only [CategoryTheory.Limits.Sigma.ι_comp_desc]
  have hC : t ≫ c.hom = w := by
    let ε : G ≃ End (SSet.FundamentalGroupoid.mk y) := e.toEquiv
    let F : SSet.{u} := (∐ fun _ : I => V)
    let fA : End (SSet.FundamentalGroupoid.mk y) → SSet.{u} := fun _ => F
    let fB : G → SSet.{u} := fA ∘ ε
    have hStock : CategoryTheory.Limits.Sigma.ι fB q ≫
        (CategoryTheory.Limits.Sigma.reindex ε fA).hom =
          CategoryTheory.Limits.Sigma.ι fA (ε q) :=
      CategoryTheory.Limits.Sigma.ι_reindex_hom ε fA q
    have ht : t = (CategoryTheory.Limits.Sigma.ι fB q : F ⟶ (∐ fB)) := rfl
    have hc : c.hom = (CategoryTheory.Limits.Sigma.reindex ε fA).hom := rfl
    have hw : w = (CategoryTheory.Limits.Sigma.ι fA (ε q) : F ⟶ (∐ fA)) := rfl
    exact (congrArg₂ (fun (s : F ⟶ (∐ fB)) (k : (∐ fB) ⟶ (∐ fA)) => s ≫ k)
      ht hc).trans (hStock.trans hw.symm)
  have hZ : w ≫ z.hom = nativeCoverCopyLift L (e q) :=
    nativeCoverPullbackCopiesIso_ι L (e q)
  change j ≫ (a.hom ≫ (b.hom ≫ (c.hom ≫ z.hom))) = r ≫ nativeCoverCopyLift L (e q)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (b.hom ≫ (c.hom ≫ z.hom))) hA).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ (c.hom ≫ z.hom)) hB).trans
          ((Category.assoc r t (c.hom ≫ z.hom)).trans
            ((congrArg (fun f => r ≫ f) ((Category.assoc t c.hom z.hom).symm.trans
              ((congrArg (fun f => f ≫ z.hom) hC).trans hZ))))))))

omit [Y.KanComplex] in
/-- Left multiplication of labels is the actual deck action on the entire pulled family. -/
theorem nativeCoverCellCopy_deck (l : I → (V ⟶ nativeCover Y y))
    (e : G ≃* End (SSet.FundamentalGroupoid.mk y)) (q r : G) (p : I) :
    nativeCoverCellCopy l e (q * r,p) =
      nativeCoverCellCopy l e (r,p) ≫ nativeCoverCopyPullbackDeck
          (nativeCoverCellFamilyLift l) (e q) := by
  let j := CategoryTheory.Limits.Sigma.ι (fun _ : I => V) p
  let L := nativeCoverCellFamilyLift l
  exact (congrArg (fun a => j ≫ nativeCoverCopyLift L a) (e.map_mul q r)).trans
    ((congrArg (fun f => j ≫ f) (nativeCoverCopyLift_deck L (e q) (e r))).trans
      (Category.assoc _ _ _).symm)

end SSet.KanComplex

end
