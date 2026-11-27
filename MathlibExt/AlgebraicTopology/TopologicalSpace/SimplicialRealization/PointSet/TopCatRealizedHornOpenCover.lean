/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AnodyneFixedBottom
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SubdivisionAnodyne
public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Mesh
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators

/-!
# Open-cover locality of realized horn lifting

Let p:E→B be continuous and let Uᵢ be an open cover of B. Suppose every restricted map
p⁻¹(Uᵢ)→Uᵢ has right lifting against the realized simplicial horn inclusions. Then p has that
right lifting property globally.

The space universe u and cover-index universe v are independent.
-/

@[expose] public section

universe u v

open CategoryTheory HomotopicalAlgebra MorphismProperty TopologicalSpace
open scoped Simplicial SSet.modelCategoryQuillen

namespace TopCat

private noncomputable def localBottom
    {D B : TopCat.{u}} {b : D ⟶ B}
    (U : Opens B) (hb : Set.range b.hom ⊆ (U : Set B)) :
    D ⟶ TopCat.of U :=
  TopCat.ofHom
    { toFun := Set.codRestrict b.hom U (fun x => hb ⟨x, rfl⟩)
      continuous_toFun := b.hom.continuous.codRestrict
        (fun x => hb ⟨x, rfl⟩) }

private noncomputable def localTop
    {H D E B : TopCat.{u}} {i : H ⟶ D} {p : E ⟶ B}
    {a : H ⟶ E} {b : D ⟶ B}
    (sq : CommSq a i p b) (U : Opens B)
    (hb : Set.range b.hom ⊆ (U : Set B)) :
    H ⟶ TopCat.of (p.hom ⁻¹' (U : Set B)) :=
  TopCat.ofHom
    { toFun := Set.codRestrict a.hom (p.hom ⁻¹' (U : Set B))
        (fun x => by
          change p.hom (a.hom x) ∈ U
          have hx := ConcreteCategory.congr_hom sq.w x
          change p.hom (a.hom x) = b.hom (i.hom x) at hx
          rw [hx]
          exact hb ⟨i.hom x, rfl⟩)
      continuous_toFun := a.hom.continuous.codRestrict (fun x => by
        change p.hom (a.hom x) ∈ U
        have hx := ConcreteCategory.congr_hom sq.w x
        change p.hom (a.hom x) = b.hom (i.hom x) at hx
        rw [hx]
        exact hb ⟨i.hom x, rfl⟩) }

private noncomputable def localRight
    {E B : TopCat.{u}} (p : E ⟶ B) (U : Opens B) :
    TopCat.of (p.hom ⁻¹' (U : Set B)) ⟶ TopCat.of U :=
  TopCat.ofHom (p.hom.restrictPreimage U)

private theorem localSq
    {H D E B : TopCat.{u}} {i : H ⟶ D} {p : E ⟶ B}
    {a : H ⟶ E} {b : D ⟶ B}
    (sq : CommSq a i p b) (U : Opens B)
    (hb : Set.range b.hom ⊆ (U : Set B)) :
    CommSq (localTop sq U hb) i (localRight p U)
      (localBottom U hb) := by
  constructor
  apply TopCat.ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom sq.w x

private noncomputable def includePreimage
    {E B : TopCat.{u}} (p : E ⟶ B) (U : Opens B) :
    TopCat.of (p.hom ⁻¹' (U : Set B)) ⟶ E :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

private noncomputable def includeOpen
    {B : TopCat.{u}} (U : Opens B) : TopCat.of U ⟶ B :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

private theorem localTop_include
    {H D E B : TopCat.{u}} {i : H ⟶ D} {p : E ⟶ B}
    {a : H ⟶ E} {b : D ⟶ B}
    (sq : CommSq a i p b) (U : Opens B)
    (hb : Set.range b.hom ⊆ (U : Set B)) :
    localTop sq U hb ≫ includePreimage p U = a := by
  apply TopCat.ext
  intro x
  rfl

private theorem localBottom_include
    {D B : TopCat.{u}} {b : D ⟶ B}
    (U : Opens B) (hb : Set.range b.hom ⊆ (U : Set B)) :
    localBottom U hb ≫ includeOpen U = b := by
  apply TopCat.ext
  intro x
  rfl

private theorem localRight_include
    {E B : TopCat.{u}} (p : E ⟶ B) (U : Opens B) :
    localRight p U ≫ includeOpen U = includePreimage p U ≫ p := by
  apply TopCat.ext
  intro x
  rfl

private noncomputable def unrestrictLift
    {H D E B : TopCat.{u}} {i : H ⟶ D} {p : E ⟶ B}
    {a : H ⟶ E} {b : D ⟶ B}
    (sq : CommSq a i p b) (U : Opens B)
    (hb : Set.range b.hom ⊆ (U : Set B))
    (l : (localSq sq U hb).LiftStruct) : sq.LiftStruct where
  l := l.l ≫ includePreimage p U
  fac_left := by
    rw [← Category.assoc, l.fac_left, localTop_include]
  fac_right := by
    rw [Category.assoc, ← localRight_include, ← Category.assoc,
      l.fac_right, localBottom_include]

private theorem transposeSSetSq
    {A B : SSet.{u}} {X Y : TopCat.{u}}
    {i : A ⟶ B} {p : X ⟶ Y}
    {u : A ⟶ TopCat.toSSet.obj X}
    {v : B ⟶ TopCat.toSSet.obj Y}
    (sq : CommSq u i (TopCat.toSSet.map p) v) :
    CommSq ((sSetTopAdj.homEquiv A X).symm u)
      (SSet.toTop.map i) p
      ((sSetTopAdj.homEquiv B Y).symm v) := by
  constructor
  exact (sSetTopAdj.homEquiv_naturality_right_square
    i v u p sq.w.symm).symm

set_option linter.unnecessarySimpa false in
private noncomputable def transposeSSetLift
    {A B : SSet.{u}} {X Y : TopCat.{u}}
    {i : A ⟶ B} {p : X ⟶ Y}
    {u : A ⟶ TopCat.toSSet.obj X}
    {v : B ⟶ TopCat.toSSet.obj Y}
    (sq : CommSq u i (TopCat.toSSet.map p) v)
    (l : (transposeSSetSq sq).LiftStruct) : sq.LiftStruct := by
  let l' := (transposeSSetSq sq).rightAdjointLiftStructEquiv
    sSetTopAdj l
  exact
    { l := l'.l
      fac_left := by simpa using l'.fac_left
      fac_right := by simpa using l'.fac_right }

private theorem transposeBottom_comp
    {A B : SSet.{u}} {Y : TopCat.{u}}
    (b : SSet.toTop.obj B ⟶ Y) (σ : A ⟶ B) :
    (sSetTopAdj.homEquiv A Y).symm
        (σ ≫ sSetTopAdj.homEquiv B Y b) =
      SSet.toTop.map σ ≫ b := by
  rw [sSetTopAdj.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply]

private theorem subdividedSq
    {A₀ B₀ Aₖ Bₖ E B : TopCat.{u}}
    {f₀ : A₀ ⟶ B₀} {fₖ : Aₖ ⟶ Bₖ} {p : E ⟶ B}
    {a₀ : A₀ ⟶ E} {b₀ : B₀ ⟶ B}
    (sq₀ : CommSq a₀ f₀ p b₀)
    (e : Arrow.mk fₖ ≅ Arrow.mk f₀) :
    CommSq (e.hom.left ≫ a₀) fₖ p (e.hom.right ≫ b₀) := by
  constructor
  rw [Category.assoc, sq₀.w, ← Category.assoc]
  have he : e.hom.left ≫ f₀ = fₖ ≫ e.hom.right := by
    exact e.hom.w
  rw [he, Category.assoc]

set_option linter.unnecessarySimpa false in
private noncomputable def transportBack
    {A₀ B₀ Aₖ Bₖ E B : TopCat.{u}}
    {f₀ : A₀ ⟶ B₀} {fₖ : Aₖ ⟶ Bₖ} {p : E ⟶ B}
    {a₀ : A₀ ⟶ E} {b₀ : B₀ ⟶ B}
    (sq₀ : CommSq a₀ f₀ p b₀)
    (e : Arrow.mk fₖ ≅ Arrow.mk f₀)
    (l : (subdividedSq sq₀ e).LiftStruct) : sq₀.LiftStruct where
  l := e.inv.right ≫ l.l
  fac_left := by
    rw [← Category.assoc]
    have he : e.inv.left ≫ fₖ = f₀ ≫ e.inv.right := by
      simpa using e.inv.w
    rw [← he, Category.assoc, l.fac_left, ← Category.assoc]
    have hid : e.inv.left ≫ e.hom.left = 𝟙 _ := by
      simpa using congrArg (fun q => q.left) e.inv_hom_id
    rw [hid]
    simp
  fac_right := by
    rw [Category.assoc, l.fac_right, ← Category.assoc]
    have hid : e.inv.right ≫ e.hom.right = 𝟙 _ := by
      simpa using congrArg (fun q => q.right) e.inv_hom_id
    rw [hid]
    simp

/-- For p:E→B in TopCat.{u}, let U:ι→Opens(B) be an open cover, with ι in an independent universe v.
If every restriction p⁻¹(Uᵢ)→Uᵢ lifts against realized horn inclusions, then p lifts against
them. -/
theorem realizedHornRLP_of_openCover
    {E B : TopCat.{u}} {p : E ⟶ B}
    {ι : Type v} (U : ι → Opens B)
    (hU : IsOpenCover U)
    (hp : ∀ i, TopCat.realizedHornInclusions.{u}.rlp
      (TopCat.ofHom (p.hom.restrictPreimage (U i)))) :
    TopCat.realizedHornInclusions.{u}.rlp p := by
  intro A₀ B₀ f₀ hf₀
  simp only [TopCat.realizedHornInclusions,
    MorphismProperty.iSup_iff] at hf₀
  obtain ⟨n, ⟨j⟩⟩ := hf₀
  let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  constructor
  intro top₀ bottom₀ sq₀
  obtain ⟨k, hcell⟩ :=
    SSet.exists_sdIter_simplex_range_subset bottom₀ U hU
  let horn := SSet.horn (n + 1) j
  let iₖ := (SSet.sdIter k).map horn.ι
  let e := SSet.toTopSdIterArrowIso horn.ι k
  let bottomₖ := e.hom.right ≫ bottom₀
  let sqₖ := subdividedSq sq₀ e
  let bS := sSetTopAdj.homEquiv _ _ bottomₖ
  let sqS := sqₖ.right_adjoint sSetTopAdj
  have hiₖ : SSet.anodyneExtensions iₖ :=
    (SSet.anodyneExtensions.horn_ι j).sdIter_map k
  have localHorn : ∀ {m : ℕ}
      (σ : (Δ[m + 1] : SSet.{u}) ⟶
        (SSet.sdIter k).obj (Δ[n + 1] : SSet.{u}))
      (ell : Fin (m + 2)),
      HasLiftingPropertyFixedBot (SSet.horn (m + 1) ell).ι
        (TopCat.toSSet.map p) (σ ≫ bS) := by
    intro m σ ell localTopS sqLocalS
    let sqLocalT := transposeSSetSq sqLocalS
    obtain ⟨a, ha⟩ := hcell σ
    have hb : Set.range
        ((sSetTopAdj.homEquiv _ _).symm (σ ≫ bS)).hom ⊆
        (U a : Set B) := by
      rw [transposeBottom_comp bottomₖ σ]
      simpa [bottomₖ, e, SSet.toTopSdIterArrowIso,
        Category.assoc] using ha
    let _ : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
    let hLocalR : HasLiftingProperty
        (SSet.toTop.map (SSet.horn (m + 1) ell).ι)
        (TopCat.ofHom (p.hom.restrictPreimage (U a))) :=
      hp a _ (TopCat.horn_mem_realizedHornInclusions (m + 1) ell)
    have hLocal : (localSq sqLocalT (U a) hb).HasLift :=
      hLocalR.sq_hasLift (localSq sqLocalT (U a) hb)
    exact CommSq.HasLift.mk'
      (transposeSSetLift sqLocalS
        (unrestrictLift sqLocalT (U a) hb
          hLocal.exists_lift.some))
  have hfixed : HasLiftingPropertyFixedBot iₖ
      (TopCat.toSSet.map p) bS :=
    hiₖ.hasLiftingPropertyFixedBot_of_simplices
      (TopCat.toSSet.map p) bS localHorn
  have hSqS : sqS.HasLift := hfixed _ sqS
  have hSqₖ : sqₖ.HasLift :=
    (sqₖ.right_adjoint_hasLift_iff sSetTopAdj).mp hSqS
  exact CommSq.HasLift.mk'
    (transportBack sq₀ e hSqₖ.exists_lift.some)

end TopCat
