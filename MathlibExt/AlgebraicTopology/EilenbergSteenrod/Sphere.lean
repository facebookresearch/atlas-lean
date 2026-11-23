/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.MayerVietorisExact
public import MathlibExt.Topology.Sphere.StandardCover

/-!
# Sphere suspension for ordinary homology theories

The standard two-set cover of a sphere gives the suspension isomorphism for
every ordinary homology theory with values in an abelian category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TopPair.OrdinaryHomologyTheory

open AlgebraicTopology AlgebraicTopology.OrderedTwoSetCover

variable {C : Type u} [Category.{v} C] [Abelian C]

private noncomputable def sphereCover (m : ℕ) : OrderedTwoSetCover.{w} where
  X := TopCat.sphere.{w} (m + 1)
  left := sphereCoverA.{w} (m + 1)
  right := sphereCoverB.{w} (m + 1)
  interior_cover := sphereCover_interiorsCover.{w} (m + 1)

private noncomputable def ioiHomotopyEquiv (Y : TopCat.{w}) :
    ContinuousMap.HomotopyEquiv
      (Y × ↥(Set.Ioi (0 : ℝ))) Y where
  toFun := (AlgebraicTopology.ioiProj Y).hom
  invFun := (AlgebraicTopology.ioiSect Y).hom
  left_inv := ⟨AlgebraicTopology.ioiContraction Y⟩
  right_inv := ⟨by
    change ((AlgebraicTopology.ioiSect Y ≫
      AlgebraicTopology.ioiProj Y).hom).Homotopy _
    rw [AlgebraicTopology.ioiSect_comp_ioiProj]
    exact ContinuousMap.Homotopy.refl _⟩

private noncomputable def equatorHomotopyEquiv (m : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥(sphereCoverA.{w} (m + 1) ∩ sphereCoverB.{w} (m + 1))
      ↥(TopCat.sphere.{w} m) :=
  (equatorHomeo.{w} m).toHomotopyEquiv |>.trans
    (ioiHomotopyEquiv
      (TopCat.of ↥(Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))) |>.trans
      ((Homeomorph.ulift.{w, 0}
        (X := ↥(Metric.sphere
          (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))).symm.toHomotopyEquiv)

private noncomputable def equatorHomologyIso
    (E : OrdinaryHomologyTheory.{u, v, w} C) (m : ℕ) (n : ℤ) :
    (E.obj.H n).obj
        (TopCat.of ((sphereCover m).left ∩ (sphereCover m).right :
          Set (sphereCover m).X)) ≅
      (E.obj.H n).obj (TopCat.sphere.{w} m) :=
  E.obj.absoluteIsoOfHomotopyEquiv (equatorHomotopyEquiv m) n

private theorem equatorHomologyIso_hom_naturality_theory
    {E F : OrdinaryHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (m : ℕ) (n : ℤ) :
    (f.hom.hom n).app
          (TopCat.of ((sphereCover m).left ∩ (sphereCover m).right :
            Set (sphereCover m).X)) ≫
        (equatorHomologyIso F m n).hom =
      (equatorHomologyIso E m n).hom ≫
        (f.hom.hom n).app (TopCat.sphere.{w} m) := by
  dsimp [equatorHomologyIso, sphereCover]
  exact TopPair.HomologyPretheory.absoluteIsoOfHomotopyEquiv_hom_naturality
    (E := E.obj) (F := F.obj)
    (X := TopCat.of ↥(sphereCoverA.{w} (m + 1) ∩ sphereCoverB.{w} (m + 1)))
    (Y := TopCat.sphere.{w} m) f.hom (equatorHomotopyEquiv m) n

private noncomputable def equatorHomologyNatIso (m : ℕ) (n : ℤ) :
    hFunctor (C := C) n ⋙
        (evaluation TopCat.{w} C).obj
          (TopCat.of ((sphereCover m).left ∩ (sphereCover m).right :
            Set (sphereCover m).X)) ≅
      hFunctor (C := C) n ⋙
        (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m) :=
  NatIso.ofComponents
    (fun E => equatorHomologyIso E m n)
    (fun {E F} f =>
      equatorHomologyIso_hom_naturality_theory (E := E) (F := F) f m n)

/-- Theory-natural abstract ordinary-homology suspension isomorphism for standard spheres. -/
noncomputable opaque sphereSuspensionNatIso
    (m k : ℕ) (hk : k ≠ 0) :
    hFunctor (C := C) ((k + 1 : ℕ) : ℤ) ⋙
        (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} (m + 1)) ≅
      hFunctor (C := C) (k : ℤ) ⋙
        (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m) := by
  let _ : ContractibleSpace ↥(sphereCover m).left := by
    dsimp [sphereCover]
    exact AlgebraicTopology.contractibleSpace_sphereCoverA.{w} (m + 1)
  let _ : ContractibleSpace ↥(sphereCover m).right := by
    dsimp [sphereCover]
    exact AlgebraicTopology.contractibleSpace_sphereCoverB.{w} (m + 1)
  let n0 : ℤ := (((k + 1 : ℕ) : ℤ) - 1)
  have hdeg : n0 = (k : ℤ) := by omega
  let e0 :
      hFunctor (C := C) ((k + 1 : ℕ) : ℤ) ⋙
          (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} (m + 1)) ≅
        hFunctor (C := C) n0 ⋙
          (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m) := by
    simpa only [sphereCover, n0] using
      (contractibleCoverMayerVietorisNatIso (C := C)
          (sphereCover m) k hk ≪≫
        equatorHomologyNatIso (C := C) m n0)
  exact hdeg ▸ e0

/-- Abstract ordinary-homology suspension isomorphism for standard spheres. -/
noncomputable def sphereSuspensionIso
    (E : OrdinaryHomologyTheory.{u, v, w} C)
    (m k : ℕ) (hk : k ≠ 0) :
    (E.H (k + 1)).obj (TopCat.sphere.{w} (m + 1)) ≅
      (E.H k).obj (TopCat.sphere.{w} m) :=
  (sphereSuspensionNatIso (C := C) m k hk).app E

@[simp]
theorem sphereSuspensionNatIso_app
    (m k : ℕ) (hk : k ≠ 0)
    (E : OrdinaryHomologyTheory.{u, v, w} C) :
    (sphereSuspensionNatIso (C := C) m k hk).app E =
      sphereSuspensionIso E m k hk := rfl

/-- The standard-sphere suspension isomorphism is natural in ordinary homology theories. -/
theorem sphereSuspensionIso_hom_naturality_theory
    {E F : OrdinaryHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (m k : ℕ) (hk : k ≠ 0) :
    (f.hom.hom ((k + 1 : ℕ) : ℤ)).app
          (TopCat.sphere.{w} (m + 1)) ≫
        (sphereSuspensionIso F m k hk).hom =
      (sphereSuspensionIso E m k hk).hom ≫
        (f.hom.hom (k : ℤ)).app (TopCat.sphere.{w} m) :=
  (sphereSuspensionNatIso (C := C) m k hk).hom.naturality f

end TopPair.OrdinaryHomologyTheory
