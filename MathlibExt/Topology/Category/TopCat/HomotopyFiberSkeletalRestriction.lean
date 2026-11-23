/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberRestriction
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationFiniteRelativeFactor
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
# Actual skeletal restrictions of compact homotopy-fiber families

The simplicial skeleton bound `d` contains dimensions strictly less than `d`.
Finite simplicial support therefore gives a bounded actual skeletal factor.
The homotopy-fiber construction retains the original total coordinate,
the lifted path and its fixed original endpoint.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet

private theorem range_le_skeleton_of_hasDimensionLT {A X : SSet.{u}}
    (f : A ⟶ X) (d : ℕ) [A.HasDimensionLT d] :
    Subcomplex.range f ≤ X.skeleton d := by
  rintro ⟨⟨m⟩⟩ x ⟨y, rfl⟩
  obtain ⟨n, α, _, z, rfl⟩ := A.exists_nonDegenerate y
  have hn := A.dim_lt_of_nonDegenerate z d
  have hnat := ConcreteCategory.congr_hom (f.naturality α.op) z.1
  change f.app (op ⦋m⦌) (A.map α.op z.1) = X.map α.op (f.app (op ⦋n⦌) z.1) at hnat
  rw [hnat]
  exact (X.skeleton d).map α.op (X.mem_skeleton (f.app (op ⦋n⦌) z.1) hn)

/-- A finite subcomplex is contained in an actual simplicial skeleton. -/
theorem Subcomplex.exists_le_skeleton_of_finite {X : SSet.{u}}
    (A : X.Subcomplex) [SSet.Finite (A : SSet.{u})] : ∃ d : ℕ, A ≤ X.skeleton d := by
  obtain ⟨d, hd⟩ := SSet.hasDimensionLT_of_finite (A : SSet.{u})
  let _ : (A : SSet.{u}).HasDimensionLT d := hd
  refine ⟨d, ?_⟩
  intro a x hx
  exact range_le_skeleton_of_hasDimensionLT A.ι d a ⟨⟨x, hx⟩, rfl⟩

/-- A compact map into the actual realization factors through an actual skeleton. -/
theorem exists_skeleton_factor_topCatHom {X : SSet.{u}} {K : TopCat.{u}} [CompactSpace K]
    (f : K ⟶ SSet.toTop.obj X) :
    ∃ (d : ℕ) (g : K ⟶ SSet.toTop.obj (X.skeleton d : SSet.{u})),
      f = g ≫ SSet.toTop.map (X.skeleton d).ι := by
  obtain ⟨A, hA, g, hg⟩ := exists_finite_subcomplex_factor_topCatHom f
  let _ : SSet.Finite (A : SSet.{u}) := hA
  obtain ⟨d, hd⟩ := A.exists_le_skeleton_of_finite
  refine ⟨d, g ≫ SSet.toTop.map (Subcomplex.homOfLE hd), ?_⟩
  rw [Category.assoc, ← SSet.toTop.map_comp, Subcomplex.homOfLE_ι]
  exact hg

/-- Compact skeletal factorization retains an exact prescribed finite restriction. -/
theorem exists_skeleton_factor_topCatHom_of_restriction
    {X : SSet.{u}} {K L : TopCat.{u}} [CompactSpace K]
    (B : X.Subcomplex) [SSet.Finite (B : SSet.{u})]
    (i : L ⟶ K) (b : L ⟶ SSet.toTop.obj (B : SSet.{u}))
    (f : K ⟶ SSet.toTop.obj X)
    (hrestrict : i ≫ f = b ≫ SSet.toTop.map B.ι) :
    ∃ (d : ℕ) (hB : B ≤ X.skeleton d)
      (g : K ⟶ SSet.toTop.obj (X.skeleton d : SSet.{u})),
      i ≫ g = b ≫ SSet.toTop.map (Subcomplex.homOfLE hB) ∧
        f = g ≫ SSet.toTop.map (X.skeleton d).ι := by
  obtain ⟨A, hA, hBA, g, hr, hf⟩ :=
    exists_finite_subcomplex_factor_topCatHom_of_restriction B inferInstance i b f hrestrict
  let _ : SSet.Finite (A : SSet.{u}) := hA
  obtain ⟨d, hd⟩ := A.exists_le_skeleton_of_finite
  refine ⟨d, hBA.trans hd, g ≫ SSet.toTop.map (Subcomplex.homOfLE hd), ?_, ?_⟩
  · rw [← Category.assoc, hr, Category.assoc, ← SSet.toTop.map_comp, Subcomplex.homOfLE_comp]
  · rw [Category.assoc, ← SSet.toTop.map_comp, Subcomplex.homOfLE_ι]
    exact hf

/-- The exact relative skeletal factor can be placed above any prescribed bound. -/
theorem exists_skeleton_factor_topCatHom_of_restriction_ge
    {X : SSet.{u}} {K L : TopCat.{u}} [CompactSpace K]
    (d₀ : ℕ) (B : X.Subcomplex) [SSet.Finite (B : SSet.{u})]
    (i : L ⟶ K) (b : L ⟶ SSet.toTop.obj (B : SSet.{u}))
    (f : K ⟶ SSet.toTop.obj X)
    (hrestrict : i ≫ f = b ≫ SSet.toTop.map B.ι) :
    ∃ (d : ℕ) (_ : d₀ ≤ d) (hB : B ≤ X.skeleton d)
      (g : K ⟶ SSet.toTop.obj (X.skeleton d : SSet.{u})),
      i ≫ g = b ≫ SSet.toTop.map (Subcomplex.homOfLE hB) ∧
        f = g ≫ SSet.toTop.map (X.skeleton d).ι := by
  obtain ⟨d, hB, g, hr, hf⟩ :=
    exists_skeleton_factor_topCatHom_of_restriction B i b f hrestrict
  have hd : d ≤ d + d₀ := Nat.le_add_right d d₀
  have hd₀ : d₀ ≤ d + d₀ := Nat.le_add_left d₀ d
  have hs := X.skeleton.monotone hd
  refine ⟨d + d₀, hd₀, hB.trans hs, g ≫ SSet.toTop.map (Subcomplex.homOfLE hs), ?_, ?_⟩
  · rw [← Category.assoc, hr, Category.assoc, ← SSet.toTop.map_comp, Subcomplex.homOfLE_comp]
  · rw [Category.assoc, ← SSet.toTop.map_comp, Subcomplex.homOfLE_ι]
    exact hf

end SSet

namespace TopCat

private theorem subcomplexPoint_inclusion {X : SSet.{u}} {A B : X.Subcomplex}
    (hAB : A ≤ B) (a : SSet.toTop.obj (A : SSet.{u})) :
    SSet.toTop.map B.ι (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) =
      SSet.toTop.map A.ι a := by
  have h : SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫ SSet.toTop.map B.ι =
      SSet.toTop.map A.ι := by
    rw [← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]
  exact ConcreteCategory.congr_hom h a

/-- The actual homotopy-fiber map of a subcomplex restriction, with its
endpoint fixed at the original carrier point in the full realization. -/
def subcomplexHomotopyFiberMap {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B : X.Subcomplex} (hAB : A ≤ B)
    (a : SSet.toTop.obj (A : SSet.{u})) :
    homotopyFiber (pullback.snd p (SSet.toTop.map B.ι))
        (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) ⟶
      homotopyFiber p (SSet.toTop.map A.ι a) :=
  homotopyPullbackMap (pullback.fst p (SSet.toTop.map B.ι)) (𝟙 (TopCat.of PUnit))
    (SSet.toTop.map B.ι) pullback.condition.symm
    (by ext x; exact subcomplexPoint_inclusion hAB a)

/-- The subcomplex homotopy-fiber map retains the actual total inclusion. -/
@[reassoc]
theorem subcomplexHomotopyFiberMap_toTotal {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B : X.Subcomplex} (hAB : A ≤ B)
    (a : SSet.toTop.obj (A : SSet.{u})) :
    subcomplexHomotopyFiberMap p hAB a ≫ homotopyFiberToTotal p (SSet.toTop.map A.ι a) =
      homotopyFiberToTotal (pullback.snd p (SSet.toTop.map B.ι))
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) ≫
        pullback.fst p (SSet.toTop.map B.ι) :=
  homotopyPullbackMap_left (pullback.fst p (SSet.toTop.map B.ι)) (𝟙 (TopCat.of PUnit))
    (SSet.toTop.map B.ι) pullback.condition.symm
    (by ext x; exact subcomplexPoint_inclusion hAB a)

/-- The path is the actual included stage path, with its original parameter. -/
@[reassoc]
theorem subcomplexHomotopyFiberMap_path {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B : X.Subcomplex} (hAB : A ≤ B)
    (a : SSet.toTop.obj (A : SSet.{u})) :
    subcomplexHomotopyFiberMap p hAB a ≫ homotopyFiberPath p (SSet.toTop.map A.ι a) =
      homotopyFiberPath (pullback.snd p (SSet.toTop.map B.ι))
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) ≫
        pathObjectMap (SSet.toTop.map B.ι) :=
  homotopyPullbackMap_path (pullback.fst p (SSet.toTop.map B.ι)) (𝟙 (TopCat.of PUnit))
    (SSet.toTop.map B.ι) pullback.condition.symm
    (by ext x; exact subcomplexPoint_inclusion hAB a)

private theorem mono_realizedSubcomplexInclusion {X : SSet.{u}} (B : X.Subcomplex) :
    Mono (SSet.toTop.map B.ι) :=
  (TopCat.mono_iff_injective _).mpr
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι B).isEmbedding.injective

private theorem pathObjectMap_mono {A B : TopCat.{u}} (i : A ⟶ B) [Mono i] :
    Mono (pathObjectMap i) := by
  have hi := (TopCat.mono_iff_injective i).mp inferInstance
  apply (TopCat.mono_iff_injective _).mpr
  intro γ δ h
  ext t
  have ht := congrArg (fun p : pathObject B => p t) h
  exact hi ht

/-- The actual stage-to-global homotopy-fiber map is mono. -/
instance subcomplexHomotopyFiberMap_mono {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B : X.Subcomplex} (hAB : A ≤ B)
    (a : SSet.toTop.obj (A : SSet.{u})) : Mono (subcomplexHomotopyFiberMap p hAB a) := by
  let _ : Mono (SSet.toTop.map B.ι) := mono_realizedSubcomplexInclusion B
  let _ : Mono (pullback.fst p (SSet.toTop.map B.ι)) := inferInstance
  let _ : Mono (pathObjectMap (SSet.toTop.map B.ι)) := pathObjectMap_mono _
  constructor
  intro T f g h
  apply homotopyPullback_hom_ext
  · apply (cancel_mono (pullback.fst p (SSet.toTop.map B.ι))).mp
    have ht := congrArg (fun k => k ≫ homotopyFiberToTotal p (SSet.toTop.map A.ι a)) h
    simpa only [Category.assoc, subcomplexHomotopyFiberMap_toTotal] using ht
  · exact isTerminalPUnit.hom_ext _ _
  · apply (cancel_mono (pathObjectMap (SSet.toTop.map B.ι))).mp
    have hp := congrArg (fun k => k ≫ homotopyFiberPath p (SSet.toTop.map A.ι a)) h
    simpa only [Category.assoc, subcomplexHomotopyFiberMap_path] using hp

/-- The actual total map between two nested base-subcomplex restrictions. -/
def subcomplexRestrictionMap {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {B C : X.Subcomplex} (hBC : B ≤ C) :
    pullback p (SSet.toTop.map B.ι) ⟶ pullback p (SSet.toTop.map C.ι) :=
  pullback.lift (pullback.fst p (SSet.toTop.map B.ι))
    (pullback.snd p (SSet.toTop.map B.ι) ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE hBC)) (by
      rw [Category.assoc, ← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]
      exact pullback.condition)

@[reassoc]
theorem subcomplexRestrictionMap_fst {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {B C : X.Subcomplex} (hBC : B ≤ C) :
    subcomplexRestrictionMap p hBC ≫ pullback.fst p (SSet.toTop.map C.ι) =
      pullback.fst p (SSet.toTop.map B.ι) := by
  rw [subcomplexRestrictionMap, pullback.lift_fst]

@[reassoc]
theorem subcomplexRestrictionMap_snd {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {B C : X.Subcomplex} (hBC : B ≤ C) :
    subcomplexRestrictionMap p hBC ≫ pullback.snd p (SSet.toTop.map C.ι) =
      pullback.snd p (SSet.toTop.map B.ι) ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE hBC) := by
  rw [subcomplexRestrictionMap, pullback.lift_snd]

/-- Nested restrictions form the actual pasted pullback square. -/
theorem subcomplexRestrictionMap_isPullback {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {B C : X.Subcomplex} (hBC : B ≤ C) :
    IsPullback (subcomplexRestrictionMap p hBC) (pullback.snd p (SSet.toTop.map B.ι))
      (pullback.snd p (SSet.toTop.map C.ι)) (SSet.toTop.map (SSet.Subcomplex.homOfLE hBC)) := by
  have hb : SSet.toTop.map (SSet.Subcomplex.homOfLE hBC) ≫ SSet.toTop.map C.ι =
      SSet.toTop.map B.ι := by rw [← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]
  have outer : IsPullback
      (subcomplexRestrictionMap p hBC ≫ pullback.fst p (SSet.toTop.map C.ι))
      (pullback.snd p (SSet.toTop.map B.ι)) p
      (SSet.toTop.map (SSet.Subcomplex.homOfLE hBC) ≫ SSet.toTop.map C.ι) := by
    rw [subcomplexRestrictionMap_fst, hb]
    exact IsPullback.of_hasPullback p (SSet.toTop.map B.ι)
  exact IsPullback.of_right outer (subcomplexRestrictionMap_snd p hBC)
    (IsPullback.of_hasPullback p (SSet.toTop.map C.ι))

private theorem subcomplexPoint_transition {X : SSet.{u}} {A B C : X.Subcomplex}
    (hAB : A ≤ B) (hBC : B ≤ C) (a : SSet.toTop.obj (A : SSet.{u})) :
    SSet.toTop.map (SSet.Subcomplex.homOfLE hBC)
        (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) =
      SSet.toTop.map (SSet.Subcomplex.homOfLE (hAB.trans hBC)) a := by
  have h : SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫
        SSet.toTop.map (SSet.Subcomplex.homOfLE hBC) =
      SSet.toTop.map (SSet.Subcomplex.homOfLE (hAB.trans hBC)) := by
    rw [← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_comp]
  exact ConcreteCategory.congr_hom h a

/-- The actual transition of restriction homotopy fibers at coherent carrier points. -/
def subcomplexHomotopyFiberTransition {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B C : X.Subcomplex} (hAB : A ≤ B) (hBC : B ≤ C)
    (a : SSet.toTop.obj (A : SSet.{u})) :
    homotopyFiber (pullback.snd p (SSet.toTop.map B.ι))
        (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) ⟶
      homotopyFiber (pullback.snd p (SSet.toTop.map C.ι))
        (SSet.toTop.map (SSet.Subcomplex.homOfLE (hAB.trans hBC)) a) :=
  homotopyPullbackMap (subcomplexRestrictionMap p hBC) (𝟙 (TopCat.of PUnit))
    (SSet.toTop.map (SSet.Subcomplex.homOfLE hBC))
    (subcomplexRestrictionMap_snd p hBC).symm
    (by ext x; exact subcomplexPoint_transition hAB hBC a)

@[reassoc]
theorem subcomplexHomotopyFiberTransition_toTotal {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B C : X.Subcomplex} (hAB : A ≤ B) (hBC : B ≤ C)
    (a : SSet.toTop.obj (A : SSet.{u})) :
    subcomplexHomotopyFiberTransition p hAB hBC a ≫
        homotopyFiberToTotal (pullback.snd p (SSet.toTop.map C.ι))
          (SSet.toTop.map (SSet.Subcomplex.homOfLE (hAB.trans hBC)) a) =
      homotopyFiberToTotal (pullback.snd p (SSet.toTop.map B.ι))
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) ≫ subcomplexRestrictionMap p hBC :=
  homotopyPullbackMap_left (subcomplexRestrictionMap p hBC) (𝟙 (TopCat.of PUnit))
    (SSet.toTop.map (SSet.Subcomplex.homOfLE hBC))
    (subcomplexRestrictionMap_snd p hBC).symm
    (by ext x; exact subcomplexPoint_transition hAB hBC a)

@[reassoc]
theorem subcomplexHomotopyFiberTransition_path {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B C : X.Subcomplex} (hAB : A ≤ B) (hBC : B ≤ C)
    (a : SSet.toTop.obj (A : SSet.{u})) :
    subcomplexHomotopyFiberTransition p hAB hBC a ≫
        homotopyFiberPath (pullback.snd p (SSet.toTop.map C.ι))
          (SSet.toTop.map (SSet.Subcomplex.homOfLE (hAB.trans hBC)) a) =
      homotopyFiberPath (pullback.snd p (SSet.toTop.map B.ι))
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) ≫
        pathObjectMap (SSet.toTop.map (SSet.Subcomplex.homOfLE hBC)) :=
  homotopyPullbackMap_path (subcomplexRestrictionMap p hBC) (𝟙 (TopCat.of PUnit))
    (SSet.toTop.map (SSet.Subcomplex.homOfLE hBC))
    (subcomplexRestrictionMap_snd p hBC).symm
    (by ext x; exact subcomplexPoint_transition hAB hBC a)

/-- The actual stage transition commutes exactly with its map to the original fiber. -/
theorem subcomplexHomotopyFiberTransition_map {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B C : X.Subcomplex} (hAB : A ≤ B) (hBC : B ≤ C)
    (a : SSet.toTop.obj (A : SSet.{u})) :
    subcomplexHomotopyFiberTransition p hAB hBC a ≫
        subcomplexHomotopyFiberMap p (hAB.trans hBC) a = subcomplexHomotopyFiberMap p hAB a := by
  apply homotopyPullback_hom_ext
  · simp only [Category.assoc, subcomplexHomotopyFiberMap_toTotal,
      subcomplexHomotopyFiberTransition_toTotal_assoc, subcomplexRestrictionMap_fst]
  · exact isTerminalPUnit.hom_ext _ _
  · simp only [Category.assoc, subcomplexHomotopyFiberMap_path,
      subcomplexHomotopyFiberTransition_path_assoc]
    rw [← pathObjectMap_comp, ← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]

instance subcomplexHomotopyFiberTransition_mono {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A B C : X.Subcomplex} (hAB : A ≤ B) (hBC : B ≤ C)
    (a : SSet.toTop.obj (A : SSet.{u})) :
    Mono (subcomplexHomotopyFiberTransition p hAB hBC a) :=
  mono_of_mono_fac (subcomplexHomotopyFiberTransition_map p hAB hBC a)

/-- Every compact family in an actual homotopy fiber factors through a
skeletal restriction above the requested bound, with the original endpoint
and both total/path coordinates retained by the actual comparison map. -/
theorem exists_skeleton_homotopyFiber_factor
    {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    (A : X.Subcomplex) [SSet.Finite (A : SSet.{u})]
    (a : SSet.toTop.obj (A : SSet.{u}))
    {K : TopCat.{u}} [CompactSpace K] (d₀ : ℕ)
    (f : K ⟶ homotopyFiber p (SSet.toTop.map A.ι a)) :
    ∃ (d : ℕ) (_ : d₀ ≤ d) (hA : A ≤ X.skeleton d)
      (g : K ⟶ homotopyFiber (pullback.snd p (SSet.toTop.map (X.skeleton d).ι))
        (SSet.toTop.map (SSet.Subcomplex.homOfLE hA) a)),
      g ≫ subcomplexHomotopyFiberMap p hA a = f := by
  let b := SSet.toTop.map A.ι a
  let P := TopCat.of (K × TopCat.I.{u})
  let _ : CompactSpace TopCat.I.{u} := TopCat.I.homeomorph.symm.compactSpace
  let _ : CompactSpace P := inferInstanceAs (CompactSpace (K × TopCat.I.{u}))
  let i₀ : K ⟶ P := TopCat.ofHom ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩
  let i₁ : K ⟶ P := TopCat.ofHom ⟨fun x => (x, 1), continuous_id.prodMk continuous_const⟩
  let φ : P ⟶ SSet.toTop.obj X :=
    TopCat.ofHom (f ≫ homotopyFiberPath p b).hom.uncurry
  have hφ₁ : i₁ ≫ φ = TopCat.const (X := K) a ≫ SSet.toTop.map A.ι := by
    have hb : f ≫ homotopyFiberPath p b ≫ pathEvalOne (SSet.toTop.obj X) =
        TopCat.const (X := K) b := by
      rw [homotopyPullbackPath_evalOne]
      ext x
      rfl
    ext x
    exact ConcreteCategory.congr_hom hb x
  obtain ⟨d, hd₀, hA, φd, hr, hf⟩ :=
    SSet.exists_skeleton_factor_topCatHom_of_restriction_ge d₀ A i₁
      (TopCat.const (X := K) a) φ hφ₁
  let B := X.skeleton d
  let j := SSet.toTop.map B.ι
  let aB := SSet.toTop.map (SSet.Subcomplex.homOfLE hA) a
  let γ : K ⟶ pathObject (SSet.toTop.obj (B : SSet.{u})) := TopCat.ofHom φd.hom.curry
  let l : K ⟶ pullback p j :=
    pullback.lift (f ≫ homotopyFiberToTotal p b) (i₀ ≫ φd) (by
      calc
        (f ≫ homotopyFiberToTotal p b) ≫ p =
            f ≫ homotopyFiberPath p b ≫ pathEvalZero (SSet.toTop.obj X) := by
          rw [Category.assoc, homotopyPullbackPath_evalZero]
        _ = i₀ ≫ φ := by ext x; rfl
        _ = (i₀ ≫ φd) ≫ j := by rw [hf, Category.assoc])
  let v : K ⟶ TopCat.of PUnit := isTerminalPUnit.from K
  have hγ₀ : γ ≫ pathEvalZero (SSet.toTop.obj (B : SSet.{u})) =
      l ≫ pullback.snd p j := by
    dsimp only [l]
    rw [pullback.lift_snd]
    ext x
    rfl
  have hγ₁ : γ ≫ pathEvalOne (SSet.toTop.obj (B : SSet.{u})) =
      v ≫ TopCat.const (X := TopCat.of PUnit) aB := by
    calc
      γ ≫ pathEvalOne (SSet.toTop.obj (B : SSet.{u})) = i₁ ≫ φd := by ext x; rfl
      _ = TopCat.const (X := K) a ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE hA) := hr
      _ = v ≫ TopCat.const (X := TopCat.of PUnit) aB := by ext x; rfl
  let g : K ⟶ homotopyFiber (pullback.snd p j) aB :=
    pullback.lift (prod.lift l v) γ (by
      apply prod.hom_ext
      · simpa [pathEndpoints, Category.assoc] using hγ₀.symm
      · simpa [pathEndpoints, Category.assoc] using hγ₁.symm)
  have hgt : g ≫ homotopyFiberToTotal (pullback.snd p j) aB = l := by
    dsimp only [g]
    rw [homotopyFiberToTotal, ← Category.assoc, pullback.lift_fst]
    exact prod.lift_fst l v
  have hgp : g ≫ homotopyFiberPath (pullback.snd p j) aB = γ := by
    dsimp only [g]
    rw [pullback.lift_snd]
  refine ⟨d, hd₀, hA, g, ?_⟩
  apply homotopyPullback_hom_ext
  · rw [Category.assoc, subcomplexHomotopyFiberMap_toTotal, ← Category.assoc, hgt]
    dsimp only [l]
    rw [pullback.lift_fst]
  · exact isTerminalPUnit.hom_ext _ _
  · rw [Category.assoc, subcomplexHomotopyFiberMap_path, ← Category.assoc, hgp]
    ext x t
    exact (ConcreteCategory.congr_hom hf (x, t)).symm

private abbrev squareHomotopyFiberMapAtPoint {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) (w : W) (b : B) (hb : h w = b) :
    homotopyFiber q w ⟶ homotopyFiber p b :=
  homotopyPullbackMap s (𝟙 (TopCat.of PUnit)) h sq.w.symm (by ext x; exact hb)

private theorem squareHomotopyFiberMapAtPoint_eq {A E W B : TopCat.{u}}
    {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) (w : W) :
    squareHomotopyFiberMapAtPoint sq w (h w) rfl =
      homotopyFiberMapOfSquare s h sq.w.symm w := by
  apply homotopyPullback_hom_ext
  · simp only [squareHomotopyFiberMapAtPoint, homotopyPullbackMap_left,
      homotopyFiberMapOfSquare_toTotal]
  · exact isTerminalPUnit.hom_ext _ _
  · simp only [squareHomotopyFiberMapAtPoint, homotopyPullbackMap_path,
      homotopyFiberMapOfSquare_path]

private theorem squareHomotopyFiberMapAtPoint_mem_of_isPullback
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : IsPullback s q p h) (w : W) (b : B) (hb : h w = b)
    (hlocal : weakHomotopyEquivalences (strictFiberToHomotopyFiber q w))
    (htarget : weakHomotopyEquivalences (strictFiberToHomotopyFiber p b)) :
    weakHomotopyEquivalences (squareHomotopyFiberMapAtPoint sq.toCommSq w b hb) := by
  subst b
  rw [squareHomotopyFiberMapAtPoint_eq]
  exact homotopyFiberMapOfSquare_mem_of_isPullback_comparisons sq w hlocal htarget

private theorem targetComparison_mem_of_squareHomotopyFiberMapAtPoint
    {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : IsPullback s q p h) (w : W) (b : B) (hb : h w = b)
    (hlocal : weakHomotopyEquivalences (strictFiberToHomotopyFiber q w))
    (hmap : weakHomotopyEquivalences (squareHomotopyFiberMapAtPoint sq.toCommSq w b hb)) :
    weakHomotopyEquivalences (strictFiberToHomotopyFiber p b) := by
  subst b
  rw [squareHomotopyFiberMapAtPoint_eq] at hmap
  let _ : IsIso (strictFiberMapOfSquare s h sq.w.symm w) :=
    isIso_strictFiberMapOfSquare_of_isPullback sq w
  apply weakHomotopyEquivalences.of_precomp _ _
    (weakHomotopyEquivalences.of_isIso (strictFiberMapOfSquare s h sq.w.symm w))
  rw [strictFiberToHomotopyFiber_naturality]
  exact weakHomotopyEquivalences.comp_mem _ _ hlocal hmap

/-- The actual transition is weak from the two stage canonical comparisons. -/
theorem subcomplexHomotopyFiberTransition_mem_of_comparisons
    {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    {A B C : X.Subcomplex} (hAB : A ≤ B) (hBC : B ≤ C)
    (a : SSet.toTop.obj (A : SSet.{u}))
    (hB : weakHomotopyEquivalences (strictFiberToHomotopyFiber
      (pullback.snd p (SSet.toTop.map B.ι))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a)))
    (hC : weakHomotopyEquivalences (strictFiberToHomotopyFiber
      (pullback.snd p (SSet.toTop.map C.ι))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE (hAB.trans hBC)) a))) :
    weakHomotopyEquivalences (subcomplexHomotopyFiberTransition p hAB hBC a) :=
  squareHomotopyFiberMapAtPoint_mem_of_isPullback (subcomplexRestrictionMap_isPullback p hBC)
    (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a)
    (SSet.toTop.map (SSet.Subcomplex.homOfLE (hAB.trans hBC)) a)
    (subcomplexPoint_transition hAB hBC a) hB hC

/-- The original fixed-point comparison follows from its stage comparison
and the weak actual stage homotopy-fiber map. -/
theorem strictFiberToHomotopyFiber_mem_of_subcomplexRestriction
    {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    {A B : X.Subcomplex} (hAB : A ≤ B) (a : SSet.toTop.obj (A : SSet.{u}))
    (hB : weakHomotopyEquivalences (strictFiberToHomotopyFiber
      (pullback.snd p (SSet.toTop.map B.ι))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a)))
    (hmap : weakHomotopyEquivalences (subcomplexHomotopyFiberMap p hAB a)) :
    weakHomotopyEquivalences (strictFiberToHomotopyFiber p (SSet.toTop.map A.ι a)) :=
  targetComparison_mem_of_squareHomotopyFiberMapAtPoint
    (IsPullback.of_hasPullback p (SSet.toTop.map B.ι))
    (SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) a) (SSet.toTop.map A.ι a)
    (subcomplexPoint_inclusion hAB a) hB hmap

end TopCat

end
