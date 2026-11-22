/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BasedPathLoop
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceContractible
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne

/-!
# Weak equivalences and strictly pointed simplicial loop maps

A simplicial map carrying a selected vertex to a selected vertex induces maps
on based paths and on their strict fibers, the simplicial loop spaces.  These
maps preserve the constant path and loop and satisfy strict identity and
composition laws.

If the original map belongs to `SSet.KanComplex.W`, so does its loop-space
map.  The proof compares the based-path fibration sequences.  Their connecting
maps are bijective because based-path spaces are contractible.  Positive
homotopy groups are checked at every loop vertex, not only the constant loop;
this is necessary because a loop space need not be connected.  Degree zero is
converted to connected components using
`KanComplex.bijective_mapπ₀_iff_bijective_mapπ_zero`.

This file concerns strict pointed equalities in one simplicial-set universe.
It defines no topological or weakly-pointed loop map, singular comparison,
homotopy-group shift, spectrum map, or Quillen Q/S specialization.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalClosed Simplicial Opposite
open scoped Simplicial

universe u

namespace SSet

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Inclusion of based paths into the full simplicial path space. -/
noncomputable abbrev basedPathIncl (X : SSet.{u})
    (x : X _⦋0⦌) : basedPath X x ⟶ pathSpace X :=
  (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι

/-- Inclusion of the strict loop fiber into the based-path space. -/
noncomputable abbrev loopSpaceIncl (X : SSet.{u})
    (x : X _⦋0⦌) : loopSpace X x ⟶ basedPath X x :=
  (Subcomplex.fiber (basedPathProj X x) x).ι

/-- A strictly pointed simplicial map induces a map on based-path spaces. -/
noncomputable def basedPathMap {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    basedPath X x ⟶ basedPath Y y :=
  Subcomplex.mapFiber ((ihom (Δ[1] : SSet.{u})).map f) f
    (pathSpace_map_eval₀ f) h

/-- The based-path map is the internal-hom map after the fiber inclusions. -/
@[simp, reassoc]
theorem basedPathMap_ι {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    basedPathMap f h ≫ basedPathIncl Y y =
      basedPathIncl X x ≫
        (ihom (Δ[1] : SSet.{u})).map f := by
  exact Subcomplex.mapFiber_ι _ _ _ _

/-- The based-path map sends the constant path to the constant path. -/
@[simp]
theorem basedPathMap_app_point {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    (basedPathMap f h).app _ (basedPathPoint X x) = basedPathPoint Y y := by
  apply Subtype.ext
  change (((ihom (Δ[1] : SSet.{u})).map f).app _
      ((constPath X).app _ x)) = (constPath Y).app _ y
  cases h
  have hnat := constPath_naturality f
  exact congrArg (fun k : X ⟶ pathSpace Y => k.app (op ⦋0⦌) x) hnat.symm

/-- The identity map induces the identity on based paths. -/
@[simp]
theorem basedPathMap_id {X : SSet.{u}} {x : X _⦋0⦌} :
    basedPathMap (𝟙 X) (rfl : (𝟙 X : X ⟶ X).app _ x = x) =
      𝟙 (basedPath X x) := by
  let _ : Mono (basedPathIncl X x) :=
    inferInstanceAs
      (Mono ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι))
  apply (cancel_mono (basedPathIncl X x)).mp
  calc
    basedPathMap (𝟙 X) _ ≫ basedPathIncl X x =
        basedPathIncl X x ≫
          (ihom (Δ[1] : SSet.{u})).map (𝟙 X) := by
            exact basedPathMap_ι (𝟙 X) rfl
    _ = basedPathIncl X x := by simp
    _ = 𝟙 (basedPath X x) ≫ basedPathIncl X x := by simp

/-- Based-path maps respect composition. -/
theorem basedPathMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} {z : Z _⦋0⦌}
    (hf : f.app _ x = y) (hg : g.app _ y = z) :
    basedPathMap (f ≫ g) (by simp [hf, hg]) =
      basedPathMap f hf ≫ basedPathMap g hg := by
  let _ : Mono (basedPathIncl Z z) :=
    inferInstanceAs
      (Mono ((Subcomplex.fiber (eval₀ : pathSpace Z ⟶ Z) z).ι))
  apply (cancel_mono (basedPathIncl Z z)).mp
  calc
    basedPathMap (f ≫ g) _ ≫ basedPathIncl Z z =
        basedPathIncl X x ≫
          (ihom (Δ[1] : SSet.{u})).map (f ≫ g) := by
            rw [basedPathMap_ι]
    _ = basedPathIncl X x ≫ ((ihom (Δ[1] : SSet.{u})).map f ≫
          (ihom (Δ[1] : SSet.{u})).map g) := by
            rw [Functor.map_comp]
    _ = (basedPathIncl X x ≫ (ihom (Δ[1] : SSet.{u})).map f) ≫
          (ihom (Δ[1] : SSet.{u})).map g := by rw [Category.assoc]
    _ = (basedPathMap f hf ≫ basedPathIncl Y y) ≫
          (ihom (Δ[1] : SSet.{u})).map g := by
            rw [basedPathMap_ι]
    _ = basedPathMap f hf ≫
          (basedPathIncl Y y ≫
            (ihom (Δ[1] : SSet.{u})).map g) := by rw [Category.assoc]
    _ = basedPathMap f hf ≫
          (basedPathMap g hg ≫ basedPathIncl Z z) := by
            rw [basedPathMap_ι]
    _ = (basedPathMap f hf ≫ basedPathMap g hg) ≫
          basedPathIncl Z z := by
          rw [Category.assoc]

/-- Naturality of final-point evaluation on based paths. -/
@[reassoc]
theorem basedPathMap_proj {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    basedPathMap f h ≫ basedPathProj Y y = basedPathProj X x ≫ f := by
  change basedPathMap f h ≫ (basedPathIncl Y y ≫ eval₁) =
    (basedPathIncl X x ≫ eval₁) ≫ f
  rw [← Category.assoc, basedPathMap_ι, Category.assoc,
    pathSpace_map_eval₁, ← Category.assoc]

/-- A strictly pointed simplicial map induces a map on strict loop spaces. -/
noncomputable def loopSpaceMap {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    loopSpace X x ⟶ loopSpace Y y :=
  Subcomplex.mapFiber (basedPathMap f h) f (basedPathMap_proj f h) h

/-- The loop map is the based-path map after the fiber inclusions. -/
@[simp, reassoc]
theorem loopSpaceMap_ι {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    loopSpaceMap f h ≫ loopSpaceIncl Y y =
      loopSpaceIncl X x ≫ basedPathMap f h := by
  exact Subcomplex.mapFiber_ι _ _ _ _

/-- The loop map sends the selected constant loop to the selected constant
loop. -/
@[simp]
theorem loopSpaceMap_app_point {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    (loopSpaceMap f h).app _ (loopFibrationSequence X x).fiberPoint =
      (loopFibrationSequence Y y).fiberPoint := by
  apply Subtype.ext
  exact basedPathMap_app_point f h

/-- The identity map induces the identity on strict loop spaces. -/
@[simp]
theorem loopSpaceMap_id {X : SSet.{u}} {x : X _⦋0⦌} :
    loopSpaceMap (𝟙 X) (rfl : (𝟙 X : X ⟶ X).app _ x = x) =
      𝟙 (loopSpace X x) := by
  let _ : Mono (loopSpaceIncl X x) :=
    inferInstanceAs (Mono ((Subcomplex.fiber (basedPathProj X x) x).ι))
  apply (cancel_mono (loopSpaceIncl X x)).mp
  calc
    loopSpaceMap (𝟙 X) _ ≫ loopSpaceIncl X x =
        loopSpaceIncl X x ≫ basedPathMap (𝟙 X) rfl := by
          exact loopSpaceMap_ι (𝟙 X) rfl
    _ = loopSpaceIncl X x := by rw [basedPathMap_id]; simp
    _ = 𝟙 (loopSpace X x) ≫ loopSpaceIncl X x := by simp

/-- Strict loop-space maps respect composition. -/
theorem loopSpaceMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} {z : Z _⦋0⦌}
    (hf : f.app _ x = y) (hg : g.app _ y = z) :
    loopSpaceMap (f ≫ g) (by simp [hf, hg]) =
      loopSpaceMap f hf ≫ loopSpaceMap g hg := by
  let _ : Mono (loopSpaceIncl Z z) :=
    inferInstanceAs (Mono ((Subcomplex.fiber (basedPathProj Z z) z).ι))
  apply (cancel_mono (loopSpaceIncl Z z)).mp
  calc
    loopSpaceMap (f ≫ g) _ ≫ loopSpaceIncl Z z =
        loopSpaceIncl X x ≫ basedPathMap (f ≫ g) _ := by
          rw [loopSpaceMap_ι]
    _ = loopSpaceIncl X x ≫
          (basedPathMap f hf ≫ basedPathMap g hg) := by
      rw [basedPathMap_comp]
    _ = (loopSpaceIncl X x ≫ basedPathMap f hf) ≫
          basedPathMap g hg := by
      rw [Category.assoc]
    _ = (loopSpaceMap f hf ≫ loopSpaceIncl Y y) ≫
          basedPathMap g hg := by
            rw [loopSpaceMap_ι]
    _ = loopSpaceMap f hf ≫
          (loopSpaceIncl Y y ≫ basedPathMap g hg) := by
      rw [Category.assoc]
    _ = loopSpaceMap f hf ≫
          (loopSpaceMap g hg ≫ loopSpaceIncl Z z) := by
            rw [loopSpaceMap_ι]
    _ = (loopSpaceMap f hf ≫ loopSpaceMap g hg) ≫
          loopSpaceIncl Z z := by
      rw [Category.assoc]

/-- A strictly pointed map induces a morphism between the corresponding
based-path fibration sequences. -/
noncomputable def loopFibrationSequenceHom {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    FibrationSequenceHom (loopFibrationSequence X x)
      (loopFibrationSequence Y y) where
  totalMap := basedPathMap f h
  baseMap := f
  comm := basedPathMap_proj f h
  total_pt := basedPathMap_app_point f h
  base_pt := h

/-- The fiber map of `loopFibrationSequenceHom` is the strict loop-space map. -/
@[simp]
theorem loopFibrationSequenceHom_fiberMap {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    (loopFibrationSequenceHom f h).fiberMap = loopSpaceMap f h :=
  rfl

private theorem subsingleton_pi_basedPath_at (X : SSet.{u})
    [KanComplex X] (x : X _⦋0⦌) (e : basedPath X x _⦋0⦌)
    (n : ℕ) : Subsingleton (KanComplex.π n (basedPath X x) e) := by
  let edge : Edge (basedPathPoint X x) e := by
    simpa using Edge.ofSimplicialObjectHomotopy
      (basedPathContraction X x).toSimplicialObjectHomotopy e
  let p : FundamentalGroupoid.mk (basedPathPoint X x) ⟶
      FundamentalGroupoid.mk e :=
    FundamentalGroupoid.homMk edge
  rw [← (KanComplex.π.actionEquiv (n := n) p).subsingleton_congr]
  exact subsingleton_pi_basedPath X x n

private noncomputable def loopFibrationSequenceAt (X : SSet.{u})
    [KanComplex X] (x : X _⦋0⦌) (z : loopSpace X x _⦋0⦌) :
    FibrationSequence.{u} where
  E := basedPath X x
  B := X
  p := basedPathProj X x
  fibration_p := inferInstance
  fibrant_B := inferInstance
  e := z.val
  b := x
  hb := (Subcomplex.mem_fiber_obj_zero_iff (basedPathProj X x) x).mp z.property

private theorem loopFibrationSequenceAt_fiberPoint (X : SSet.{u})
    [KanComplex X] (x : X _⦋0⦌) (z : loopSpace X x _⦋0⦌) :
    (loopFibrationSequenceAt X x z).fiberPoint = z := by
  apply Subtype.ext
  rfl

private noncomputable def loopFibrationSequenceHomAt
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (h : f.app _ x = y) (z : loopSpace X x _⦋0⦌) :
    FibrationSequenceHom (loopFibrationSequenceAt X x z)
      (loopFibrationSequenceAt Y y ((loopSpaceMap f h).app _ z)) where
  totalMap := basedPathMap f h
  baseMap := f
  comm := basedPathMap_proj f h
  total_pt := by rfl
  base_pt := h

private theorem bijective_of_bijective_connecting_square_bottom
    {A B C D : Type u} (sourceConnecting : A → B)
    (targetConnecting : C → D) (topMap : A → C)
    (bottomMap : B → D)
    (hSource : Function.Bijective sourceConnecting)
    (hTarget : Function.Bijective targetConnecting)
    (hTop : Function.Bijective topMap)
    (hcomm : ∀ a, bottomMap (sourceConnecting a) =
      targetConnecting (topMap a)) :
    Function.Bijective bottomMap := by
  constructor
  · intro b₁ b₂ hb
    obtain ⟨a₁, rfl⟩ := hSource.2 b₁
    obtain ⟨a₂, rfl⟩ := hSource.2 b₂
    apply congrArg sourceConnecting
    apply hTop.1
    apply hTarget.1
    rw [← hcomm, ← hcomm]
    exact hb
  · intro d
    obtain ⟨c, hc⟩ := hTarget.2 d
    obtain ⟨a, ha⟩ := hTop.2 c
    refine ⟨sourceConnecting a, ?_⟩
    rw [hcomm, ha, hc]

private theorem bijective_piMap_of_basepoints_eq
    {A B : SSet.{u}} {g : A ⟶ B}
    {a₁ a₂ : A _⦋0⦌} {b₁ b₂ : B _⦋0⦌}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (h₁ : g.app _ a₁ = b₁) (h₂ : g.app _ a₂ = b₂)
    (n : ℕ)
    (h : Function.Bijective (KanComplex.π.map g h₁ n)) :
    Function.Bijective (KanComplex.π.map g h₂ n) := by
  subst a₂
  subst b₂
  exact h

/-- A weak equivalence induces bijections on every pointed homotopy group of
strict loop spaces, at every source loop vertex. -/
theorem KanComplex.W.loopSpaceMap_bijective_pi
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : KanComplex.W f)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : loopSpace X x _⦋0⦌) (n : ℕ) :
    Function.Bijective
      (KanComplex.π.map (SSet.loopSpaceMap f h) rfl n (x := z)) := by
  subst y
  let _ : KanComplex X := hf.kanComplex_source
  let _ : KanComplex Y := hf.kanComplex_target
  let S := loopFibrationSequenceAt X x z
  let z' := (SSet.loopSpaceMap f rfl).app (op ⦋0⦌) z
  let T := loopFibrationSequenceAt Y (f.app (op ⦋0⦌) x) z'
  let F := loopFibrationSequenceHomAt f rfl z
  have hSource : Function.Bijective (S.connectingMap n) := by
    apply S.connectingMap_bijective_of_subsingleton_total
    intro k
    simpa [S, loopFibrationSequenceAt] using
      subsingleton_pi_basedPath_at X x z.val k
  have hTarget : Function.Bijective (T.connectingMap n) := by
    apply T.connectingMap_bijective_of_subsingleton_total
    intro k
    simpa [T, z', loopFibrationSequenceAt] using
      subsingleton_pi_basedPath_at Y (f.app (op ⦋0⦌) x) z'.val k
  have hTop : Function.Bijective
      (KanComplex.π.map f rfl (n + 1) (x := x)) :=
    hf.bijective_piMap (n + 1) x
  have hBottom : Function.Bijective
      (KanComplex.π.map F.fiberMap F.fiberMap_app_basePoint n) := by
    apply bijective_of_bijective_connecting_square_bottom
      (S.connectingMap n) (T.connectingMap n)
      (KanComplex.π.map f rfl (n + 1))
      (KanComplex.π.map F.fiberMap F.fiberMap_app_basePoint n)
      hSource hTarget hTop
    intro q
    exact FibrationSequence.connectingMap_naturality F q
  let a₁ : loopSpace X x _⦋0⦌ := S.fiberPoint
  let b₁ : loopSpace Y (f.app (op ⦋0⦌) x) _⦋0⦌ := T.fiberPoint
  have ha : a₁ = z := loopFibrationSequenceAt_fiberPoint X x z
  have hb : b₁ = z' :=
    loopFibrationSequenceAt_fiberPoint Y (f.app (op ⦋0⦌) x) z'
  have hMap₁ : (SSet.loopSpaceMap f rfl).app _ a₁ = b₁ := by
    apply Subtype.ext
    rfl
  have hBottom' : Function.Bijective
      (KanComplex.π.map (SSet.loopSpaceMap f rfl) hMap₁ n) := by
    simpa [a₁, b₁, S, T, F, z', loopFibrationSequenceAt, loopSpace,
      loopFibrationSequenceHomAt, FibrationSequence.fiber,
      FibrationSequenceHom.fiberMap, FibrationSequence.fiberPoint,
      Subcomplex.fiber.basePoint, SSet.loopSpaceMap] using hBottom
  exact bijective_piMap_of_basepoints_eq ha hb hMap₁ rfl n hBottom'

/-- A strictly pointed simplicial loop map preserves weak equivalences between
Kan complexes. -/
theorem KanComplex.W.loopSpaceMap
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : KanComplex.W f)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    KanComplex.W (SSet.loopSpaceMap f h) := by
  let _ : KanComplex X := hf.kanComplex_source
  let _ : KanComplex Y := hf.kanComplex_target
  rw [KanComplex.W_iff]
  constructor
  · let z := (loopFibrationSequence X x).fiberPoint
    apply (KanComplex.bijective_mapπ₀_iff_bijective_mapπ_zero
      (SSet.loopSpaceMap f h) z
        ((SSet.loopSpaceMap f h).app (op ⦋0⦌) z) rfl).mp
    exact hf.loopSpaceMap_bijective_pi h z 0
  · intro n z
    exact hf.loopSpaceMap_bijective_pi h z (n + 1)

end SSet
