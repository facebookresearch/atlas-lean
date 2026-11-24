/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatExtensionStabilization
public import MathlibExt.KTheory.Ring.StableElementary.Basic
public import MathlibExt.KTheory.Ring.StableElementary.Inclusions
public import MathlibExt.KTheory.Ring.StableGeneralLinear.Stabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinearStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementarySubgroup
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Local

/-! # Stable Matsumoto extension diagram

The shifted `ℕ`-indexed diagram of paired left-extension subgroups and its
filtered colimit.  Stage `k` is `leftExtensionSubgroup F (k+2)`; successors are
the injective `leftExtensionSuccHom`.  A finite-stage projection to `StableE F`
via the field-specific `SL → E` bridge and `StableE.fromFinite` assembles, by
`NatTrans.ofSequence` and `colimitCoconeIsColimit`, into the stable projection.

Central inclusion at stage `0` (`n=2`) yields the stable central map.
-/

@[expose] public section

open CategoryTheory Limits
open Matrix.GeneralLinearGroup
open MatsumotoTitsBruhatFiber
open AlgebraicKTheory

universe u

noncomputable section

namespace MatsumotoTitsBruhatFiber

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-! ### 1. `SL → E` bridge over commutative local rings -/

/-- `SLₙ(R) →* Eₙ(R)` over a commutative local ring, rank-generic.
Over such a ring `SLₙ = Eₙ` via `det = 1`. -/
noncomputable def slToElementaryHom (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) R →*
      elementarySubgroup (Fin n) R where
  toFun g :=
    ⟨(Matrix.SpecialLinearGroup.toGL g :
        Matrix.GeneralLinearGroup (Fin n) R),
      by
        have hdet :
            Matrix.GeneralLinearGroup.det
              (Matrix.SpecialLinearGroup.toGL (n := Fin n) g) = 1 :=
          Matrix.SpecialLinearGroup.coeToGL_det g
        exact
          Matrix.GeneralLinearGroup.mem_elementarySubgroup_of_det_eq_one_of_isLocalRing
            hdet⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_slToElementaryHom (n : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin n) R) :
    (↑(slToElementaryHom R n g) :
      Matrix.GeneralLinearGroup (Fin n) R) =
      (Matrix.SpecialLinearGroup.toGL g :
        Matrix.GeneralLinearGroup (Fin n) R) :=
  rfl

theorem slToElementaryHom_injective (n : ℕ) :
    Function.Injective (slToElementaryHom (R := R) n) := by
  intro a b h
  have hGL :
      (Matrix.SpecialLinearGroup.toGL a :
        Matrix.GeneralLinearGroup (Fin n) R) =
        (Matrix.SpecialLinearGroup.toGL b :
          Matrix.GeneralLinearGroup (Fin n) R) := by
    have hval : (slToElementaryHom R n a).val =
        (slToElementaryHom R n b).val :=
      congrArg Subtype.val h
    simpa using hval
  exact Matrix.SpecialLinearGroup.toGL_injective hGL

theorem slToElementaryHom_surjective (n : ℕ) :
    Function.Surjective (slToElementaryHom (R := R) n) := by
  intro e
  have hdet :
      Matrix.GeneralLinearGroup.det
          (e.val : Matrix.GeneralLinearGroup (Fin n) R) = 1 :=
    Matrix.GeneralLinearGroup.det_of_mem_elementarySubgroup e.prop
  have hMatDet : Matrix.det (e.val : Matrix (Fin n) (Fin n) R) = 1 := by
    have h_val :
        (Matrix.GeneralLinearGroup.det
            (e.val : Matrix.GeneralLinearGroup (Fin n) R)).val =
          (1 : Rˣ).val :=
      congrArg Units.val hdet
    have h_det_val :
        (Matrix.GeneralLinearGroup.det
            (e.val : Matrix.GeneralLinearGroup (Fin n) R)).val =
          (e.val : Matrix (Fin n) (Fin n) R).det := rfl
    have h_one_val : (1 : Rˣ).val = (1 : R) := rfl
    rw [h_det_val, h_one_val] at h_val
    exact h_val
  let g : Matrix.SpecialLinearGroup (Fin n) R :=
    ⟨(e.val : Matrix (Fin n) (Fin n) R), hMatDet⟩
  use g
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.toGL g = e.val
  apply Units.ext
  rfl

theorem slToElementaryHom_bijective (n : ℕ) :
    Function.Bijective (slToElementaryHom (R := R) n) :=
  ⟨slToElementaryHom_injective R n, slToElementaryHom_surjective R n⟩

@[simp]
theorem slToElementaryHom_stabilization (n : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin n) R) :
    slToElementaryHom R (n + 1)
        (Matrix.SpecialLinearGroup.stabilization R g) =
      (ElementarySubgroup.stabilization (R := R) (k := n))
        (slToElementaryHom R n g) := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.toGL_stabilization]

end MatsumotoTitsBruhatFiber

namespace MatsumotoStableExtensionDiagram

variable (F : Type u) [Field F]

/-! ### 2. Shifted `ℕ ⥤ GrpCat` diagram -/

/-- Shifted diagram: stage `k` is `leftExtensionSubgroup F (k+2)`. -/
noncomputable def leftExtensionDiagram : ℕ ⥤ GrpCat.{u} :=
  CategoryTheory.Functor.ofSequence
    (X := fun k =>
      GrpCat.of (MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2)))
    (fun k =>
      GrpCat.ofHom
        (MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2) (by omega)))

@[simp]
theorem leftExtensionDiagram_obj (k : ℕ) :
    (leftExtensionDiagram F).obj k =
      GrpCat.of
        (MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2)) :=
  rfl

@[simp]
theorem leftExtensionDiagram_map_succ (k : ℕ) :
    (leftExtensionDiagram F).map (homOfLE (Nat.le_add_right k 1)) =
      GrpCat.ofHom
        (MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2)
          (by omega)) :=
  CategoryTheory.Functor.ofSequence_map_homOfLE_succ _ k

/-! ### 3. Filtered-colimit group and stage inclusions -/

/-- Filtered-colimit of the shifted diagram. -/
noncomputable def stableExtensionColimit : GrpCat.{u} :=
  (GrpCat.FilteredColimits.colimitCocone
    (F := leftExtensionDiagram F)).pt

/-- Underlying type of the colimit. -/
abbrev StableExtensionGroup : Type u :=
  (stableExtensionColimit (F := F) : Type u)

/-- Canonical stage inclusion `leftExtensionSubgroup F (k+2) → StableExtension`. -/
noncomputable def stableExtensionIncl (k : ℕ) :
    (leftExtensionDiagram F).obj k ⟶ stableExtensionColimit F :=
  (GrpCat.FilteredColimits.colimitCocone
    (F := leftExtensionDiagram F)).ι.app k

/-- Inclusions intertwine successors. -/
theorem stableExtensionIncl_succ (k : ℕ)
    (p : MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2)) :
    (stableExtensionIncl F (k + 1)
        (MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2)
          (by omega) p) : StableExtensionGroup F) =
      (stableExtensionIncl F k p : StableExtensionGroup F) := by
  change GrpCat.FilteredColimits.G.mk (F := leftExtensionDiagram F)
      ⟨k + 1,
        MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2)
          (by omega) p⟩ =
    GrpCat.FilteredColimits.G.mk (F := leftExtensionDiagram F) ⟨k, p⟩
  apply GrpCat.FilteredColimits.G.mk_eq
  refine ⟨k + 2, homOfLE (Nat.le_add_right (k + 1) 1),
    homOfLE (by omega : k ≤ k + 2), ?_⟩
  have h_comp :
      (homOfLE (by omega : k ≤ k + 2) : k ⟶ k + 2) =
        homOfLE (Nat.le_add_right k 1) ≫
          homOfLE (Nat.le_add_right (k + 1) 1) :=
    Subsingleton.elim _ _
  rw [h_comp, Functor.map_comp]
  simp only [leftExtensionDiagram_map_succ]
  rfl

/-! ### 4. Finite-stage projection to `StableE F` -/

/-- Finite-stage projection: `leftExtension → SL → E → StableE`. -/
noncomputable def leftExtensionStageProj (k : ℕ) :
    MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2) →*
      StableE F :=
  (StableE.fromFinite F (k + 2)).comp
    ((MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)).comp
      (MatsumotoTitsBruhatFiber.leftExtensionProjHom F (k + 2)))

theorem leftExtensionStageProj_apply (k : ℕ)
    (p : MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2)) :
    leftExtensionStageProj F k p =
      StableE.fromFinite F (k + 2)
        (MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
          (MatsumotoTitsBruhatFiber.leftExtensionProjHom F (k + 2) p)) :=
  rfl

/-- Compatibility with the stabilization successor. -/
theorem leftExtensionStageProj_succ (k : ℕ)
    (p : MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2)) :
    leftExtensionStageProj F (k + 1)
        (MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2)
          (by omega) p) =
      leftExtensionStageProj F k p := by
  simp only [leftExtensionStageProj, MonoidHom.comp_apply,
    MatsumotoTitsBruhatFiber.leftExtensionProjHom_apply]
  have h_proj :
      (MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2)
          (by omega) p).val.1 =
        Matrix.SpecialLinearGroup.stabilization F p.val.1 :=
    MatsumotoTitsBruhatFiber.leftExtensionSuccHom_proj
      F (k + 2) (by omega) p
  rw [h_proj]
  have h_sl :
      MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 3)
          (Matrix.SpecialLinearGroup.stabilization F p.val.1) =
        ElementarySubgroup.stabilization (R := F) (k := k + 2)
          (MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
            p.val.1) :=
    MatsumotoTitsBruhatFiber.slToElementaryHom_stabilization
      F (k + 2) p.val.1
  rw [h_sl]
  have h_fromFinite :
      StableE.fromFinite F (k + 3)
          (ElementarySubgroup.stabilization (R := F) (k := k + 2)
            (MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
              p.val.1)) =
        StableE.fromFinite F (k + 2)
          (MatsumotoTitsBruhatFiber.slToElementaryHom F (k + 2)
            p.val.1) := by
    apply Subtype.ext
    simp only [StableE.coe_fromFinite,
      ElementarySubgroup.coe_stabilization,
      StableGL.of_stabilization]
  exact h_fromFinite

/-! ### 5. Cocone and induced stable projection -/

/-- Cocone from the shifted diagram to `StableE F` via stage projections. -/
noncomputable def leftExtensionStableCocone :
    CategoryTheory.Limits.Cocone (leftExtensionDiagram F) where
  pt := GrpCat.of (StableE F)
  ι :=
    CategoryTheory.NatTrans.ofSequence
      (app := fun k =>
        GrpCat.ofHom (leftExtensionStageProj F k))
      (naturality := fun k => by
        ext p
        simp only [leftExtensionDiagram_map_succ]
        exact leftExtensionStageProj_succ F k p)

/-- Induced homomorphism from the filtered colimit to `StableE F`. -/
noncomputable def stableProjection :
    stableExtensionColimit F ⟶ GrpCat.of (StableE F) :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit
      (F := leftExtensionDiagram F)).desc
    (leftExtensionStableCocone F)

/-- Formula of `stableProjection` on stage inclusions. -/
theorem stableProjection_ι (k : ℕ)
    (p : MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2)) :
    (stableProjection F).hom
        ((stableExtensionIncl F k).hom p) =
      leftExtensionStageProj F k p := by
  have h_fac :=
    (GrpCat.FilteredColimits.colimitCoconeIsColimit
        (F := leftExtensionDiagram F)).fac
      (leftExtensionStableCocone F) k
  have h_pointwise :=
    DFunLike.congr_fun
      (congrArg GrpCat.Hom.hom h_fac) p
  -- `h_fac : ι.app k ≫ desc = cocone.ι.app k`
  simp only [stableProjection, stableExtensionIncl] at h_pointwise ⊢
  exact h_pointwise

/-! ### 6. Injectivity of diagram transitions and stage inclusions -/

private theorem leftExtensionDiagram_map_injective_aux
    {n m : ℕ} (f : n ⟶ m) :
    Function.Injective ((leftExtensionDiagram F).map f) := by
  induction m generalizing n with
  | zero =>
    have h_le : n ≤ 0 := leOfHom f
    have h_eq : n = 0 := Nat.le_zero.mp h_le
    subst h_eq
    have h_f : f = 𝟙 (0 : ℕ) := Subsingleton.elim f (𝟙 (0 : ℕ))
    rw [h_f]
    have h_map :
        (leftExtensionDiagram F).map (𝟙 (0 : ℕ)) =
          𝟙 ((leftExtensionDiagram F).obj 0) := by simp
    rw [h_map]
    exact Function.injective_id
  | succ m ih =>
    have h_le : n ≤ m + 1 := leOfHom f
    by_cases h_nm : n ≤ m
    · let f₁ : n ⟶ m := homOfLE h_nm
      let f₂ : m ⟶ m + 1 := homOfLE (Nat.le_add_right m 1)
      have h_eq : f = f₁ ≫ f₂ := Subsingleton.elim _ _
      have h_map_eq :
          (leftExtensionDiagram F).map f =
            (leftExtensionDiagram F).map f₁ ≫
              (leftExtensionDiagram F).map f₂ := by
        rw [h_eq, Functor.map_comp]
      have h_succ :
          (leftExtensionDiagram F).map f₂ =
            GrpCat.ofHom
              (MatsumotoTitsBruhatFiber.leftExtensionSuccHom
                F (m + 2) (by omega)) := by
        exact leftExtensionDiagram_map_succ (F := F) m
      have h_inj_f₂ :
          Function.Injective ((leftExtensionDiagram F).map f₂) := by
        rw [h_succ]
        exact
          MatsumotoTitsBruhatFiber.leftExtensionSuccHom_injective
            F (m + 2) (by omega)
      intro x y hxy
      have hxy' :
          ((leftExtensionDiagram F).map f) x =
            ((leftExtensionDiagram F).map f) y := hxy
      rw [h_map_eq] at hxy'
      have h_comp_x :
          ((leftExtensionDiagram F).map f₁ ≫
              (leftExtensionDiagram F).map f₂) x =
            ((leftExtensionDiagram F).map f₂)
              (((leftExtensionDiagram F).map f₁) x) := by
        rw [GrpCat.comp_apply]
      have h_comp_y :
          ((leftExtensionDiagram F).map f₁ ≫
              (leftExtensionDiagram F).map f₂) y =
            ((leftExtensionDiagram F).map f₂)
              (((leftExtensionDiagram F).map f₁) y) := by
        rw [GrpCat.comp_apply]
      rw [h_comp_x, h_comp_y] at hxy'
      have h_inj_f₁ :
          Function.Injective ((leftExtensionDiagram F).map f₁) :=
        ih f₁
      exact h_inj_f₁ (h_inj_f₂ hxy')
    · have h_eq : n = m + 1 := by omega
      subst h_eq
      have h_f : f = 𝟙 (m + 1 : ℕ) := Subsingleton.elim f (𝟙 _)
      rw [h_f]
      have h_map :
          (leftExtensionDiagram F).map (𝟙 (m + 1 : ℕ)) =
            𝟙 ((leftExtensionDiagram F).obj (m + 1)) := by simp
      rw [h_map]
      exact Function.injective_id

theorem leftExtensionDiagram_map_injective
    {n m : ℕ} (f : n ⟶ m) :
    Function.Injective ((leftExtensionDiagram F).map f) :=
  leftExtensionDiagram_map_injective_aux (F := F) f

/-- Every diagram transition is injective (succinct alias). -/
theorem leftExtensionSuccHomDiagram_injective
    (k : ℕ) :
    Function.Injective
      ((leftExtensionDiagram F).map
        (homOfLE (Nat.le_add_right k 1))) := by
  rw [leftExtensionDiagram_map_succ]
  exact MatsumotoTitsBruhatFiber.leftExtensionSuccHom_injective
    F (k + 2) (by omega)

/-- Canonical stage inclusions into the colimit are injective. -/
theorem stableExtensionIncl_injective (k : ℕ) :
    Function.Injective (stableExtensionIncl F k) := by
  intro x y h
  have h_mk :
      GrpCat.FilteredColimits.G.mk (F := leftExtensionDiagram F)
          ⟨k, x⟩ =
        GrpCat.FilteredColimits.G.mk (F := leftExtensionDiagram F)
          ⟨k, y⟩ := h
  have h_mk' :
      ((leftExtensionDiagram F ⋙ forget GrpCat.{u}).ιColimitType k) x =
        ((leftExtensionDiagram F ⋙ forget GrpCat.{u}).ιColimitType k) y :=
    h_mk
  have h_iff :=
    (Functor.ιColimitType_eq_iff_of_isFiltered
        (F := leftExtensionDiagram F ⋙ forget GrpCat.{u}) x y).mp
      h_mk'
  obtain ⟨l, f₁, f₂, hf⟩ := h_iff
  have h_feq : f₁ = f₂ := Subsingleton.elim _ _
  rw [h_feq] at hf
  exact leftExtensionDiagram_map_injective (F := F) f₁ hf

/-! ### 7. Stable central inclusion -/

/-- Iterated successor from stage `0` (`n=2`) to stage `k`. -/
noncomputable def leftExtensionIteratedSucc (k : ℕ) :
    MatsumotoTitsBruhatFiber.leftExtensionSubgroup F 2 →*
      MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2) :=
  ((leftExtensionDiagram F).map
      (homOfLE (Nat.zero_le k))).hom

@[simp]
theorem leftExtensionIteratedSucc_zero :
    leftExtensionIteratedSucc F 0 = MonoidHom.id _ := by
  unfold leftExtensionIteratedSucc
  simp

theorem leftExtensionIteratedSucc_succ (k : ℕ) (x) :
    leftExtensionIteratedSucc F (k + 1) x =
      MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2)
          (by omega) (leftExtensionIteratedSucc F k x) := by
  change ((leftExtensionDiagram F).map
      (homOfLE (Nat.zero_le (k + 1)))).hom x =
    (MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2)
        (by omega))
      (((leftExtensionDiagram F).map
        (homOfLE (Nat.zero_le k))).hom x)
  have h_comp :
      (homOfLE (Nat.zero_le (k + 1)) : (0 : ℕ) ⟶ k + 1) =
        (homOfLE (Nat.zero_le k) : (0 : ℕ) ⟶ k) ≫
          homOfLE (Nat.le_add_right k 1) :=
    Subsingleton.elim _ _
  have h_map :
      (leftExtensionDiagram F).map
          (homOfLE (Nat.zero_le (k + 1))) =
        (leftExtensionDiagram F).map (homOfLE (Nat.zero_le k)) ≫
          (leftExtensionDiagram F).map
            (homOfLE (Nat.le_add_right k 1)) := by
    rw [h_comp, Functor.map_comp]
  have h_app :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom h_map) x
  simp only [leftExtensionDiagram_map_succ] at h_app
  exact h_app

/-- Stable central inclusion from `MilnorK F 2`. -/
noncomputable def stableCentralHom :
    Multiplicative (MilnorK F 2) →* StableExtensionGroup F :=
  (stableExtensionIncl F 0).hom.comp
    (MatsumotoTitsBruhatFiber.centralPairHom F 2)

theorem stableCentralHom_apply
    (c : Multiplicative (MilnorK F 2)) :
    stableCentralHom F c =
      (stableExtensionIncl F 0)
        (MatsumotoTitsBruhatFiber.centralPairHom F 2 c) :=
  rfl

/-- Finite-stage central formula: iterated successor on the central pair equals the central pair
at the target rank. -/
theorem leftExtensionIteratedSucc_central (k : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    leftExtensionIteratedSucc F k
        (MatsumotoTitsBruhatFiber.centralPairHom F 2 c) =
      MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c := by
  induction k with
  | zero =>
    simp [leftExtensionIteratedSucc_zero]
  | succ k ih =>
    rw [leftExtensionIteratedSucc_succ, ih]
    -- unfold `centralPairHom` to the explicit pair, then apply the successor lemma
    change
      MatsumotoTitsBruhatFiber.leftExtensionSuccHom F (k + 2) (by omega)
          (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) =
        MatsumotoTitsBruhatFiber.centralPairHom F (k + 2 + 1) c
    have h_explicit :
        MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c =
          (⟨((1 : Matrix.SpecialLinearGroup (Fin (k + 2)) F),
              MatsumotoTitsBruhatFiber.centralPerm (F := F) c),
            MatsumotoTitsBruhatFiber.centralPair_mem_leftExtensionSubgroup
              (F := F) (n := k + 2) c⟩ :
            MatsumotoTitsBruhatFiber.leftExtensionSubgroup F (k + 2)) := rfl
    rw [h_explicit,
      MatsumotoTitsBruhatFiber.leftExtensionSuccHom_central]
    rfl

/-- Coherence with iterated successors. -/
theorem stableCentralHom_coherence (k : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    (stableExtensionIncl F k)
        (leftExtensionIteratedSucc F k
          (MatsumotoTitsBruhatFiber.centralPairHom F 2 c)) =
      stableCentralHom F c := by
  induction k with
  | zero =>
    simp only [leftExtensionIteratedSucc_zero, stableCentralHom_apply,
      MonoidHom.id_apply]
  | succ k ih =>
    rw [leftExtensionIteratedSucc_succ]
    have h_succ :=
      stableExtensionIncl_succ F k
        (leftExtensionIteratedSucc F k
          (MatsumotoTitsBruhatFiber.centralPairHom F 2 c))
    rw [h_succ]
    exact ih

/-- Direct stable coherence: the stage inclusion of the central pair
equals the stable central map. -/
theorem stableExtensionIncl_central (k : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    (stableExtensionIncl F k)
        (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c) =
      stableCentralHom F c := by
  have h_iter := leftExtensionIteratedSucc_central F k c
  have h_coh := stableCentralHom_coherence F k c
  calc (stableExtensionIncl F k)
          (MatsumotoTitsBruhatFiber.centralPairHom F (k + 2) c)
      = (stableExtensionIncl F k)
          (leftExtensionIteratedSucc F k
            (MatsumotoTitsBruhatFiber.centralPairHom F 2 c)) := by
          rw [← h_iter]
    _ = stableCentralHom F c := h_coh

theorem stableCentralHom_injective :
    Function.Injective (stableCentralHom (F := F)) := by
  intro c₁ c₂ h
  have h_inj :=
    stableExtensionIncl_injective (F := F) 0
  have h_eq :
      MatsumotoTitsBruhatFiber.centralPairHom F 2 c₁ =
        MatsumotoTitsBruhatFiber.centralPairHom F 2 c₂ :=
    h_inj h
  exact
    MatsumotoTitsBruhatFiber.centralPairHom_injective
      (F := F) (n := 2) h_eq

theorem stableProjection_central (c : Multiplicative (MilnorK F 2)) :
    (stableProjection F).hom (stableCentralHom F c) = 1 := by
  have h_proj_central :
      leftExtensionStageProj F 0
          (MatsumotoTitsBruhatFiber.centralPairHom F 2 c) = 1 := by
    simp only [leftExtensionStageProj, MonoidHom.comp_apply,
      MatsumotoTitsBruhatFiber.leftExtensionProjHom_apply,
      MatsumotoTitsBruhatFiber.centralPairHom_val]
    simp
  have h_stable :=
    stableProjection_ι F 0
      (MatsumotoTitsBruhatFiber.centralPairHom F 2 c)
  calc (stableProjection F).hom (stableCentralHom F c)
      = (stableProjection F).hom
          ((stableExtensionIncl F 0).hom
            (MatsumotoTitsBruhatFiber.centralPairHom F 2 c)) := rfl
    _ = leftExtensionStageProj F 0
          (MatsumotoTitsBruhatFiber.centralPairHom F 2 c) := h_stable
    _ = 1 := h_proj_central

/-- The stable projection kills the central inclusion (bundled form). -/
theorem stableProjection_comp_stableCentralHom :
    (stableProjection F).hom.comp (stableCentralHom F) = 1 := by
  apply MonoidHom.ext
  intro c
  exact stableProjection_central F c

end MatsumotoStableExtensionDiagram

end
