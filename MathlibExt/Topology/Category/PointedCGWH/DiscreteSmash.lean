/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.DiscreteGroupActions
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.CategoryTheory.Action.Coinvariants
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Native discrete smash coefficient coproducts and balancing arrows
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w wH wG

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace PointedCGWH

/-- The freely based point is the actual selected native smash unit. -/
private def nativeFreePointUnitIso :
    (Under.costar CGWH.point.{u, v}).obj CGWH.point ≅
      𝟙_ PointedCGWH.{u, v} :=
  Iso.refl ((Under.costar CGWH.point.{u, v}).obj CGWH.point)

/-- Fixed-right smash of that actual free point is the original coefficient. -/
private def nativeCoefficientUnitIso (Z : PointedCGWH.{u, v}) :
    (tensorRight Z).obj ((Under.costar CGWH.point.{u, v}).obj CGWH.point) ≅ Z :=
  (tensorRight Z).mapIso nativeFreePointUnitIso.{u, v} ≪≫ λ_ Z

/-- Tensor composition is used in its forward direction at explicitly typed objects. -/
private theorem nativeTensorRight_comp {X Y Y' : PointedCGWH.{u, v}}
    (Z : PointedCGWH.{u, v}) (f : X ⟶ Y) (g : Y ⟶ Y') :
    (tensorRight Z).map f ≫ (g ⊗ₘ 𝟙 Z) = (tensorRight Z).map (f ≫ g) := by
  calc
    (tensorRight Z).map f ≫ (g ⊗ₘ 𝟙 Z) =
        (f ⊗ₘ 𝟙 Z) ≫ (g ⊗ₘ 𝟙 Z) :=
      congrArg (fun h : X ⊗ Z ⟶ Y ⊗ Z => h ≫ (g ⊗ₘ 𝟙 Z))
        (tensorHom_id f Z).symm
    _ = (f ≫ g) ⊗ₘ 𝟙 Z :=
      (tensorHom_comp_tensorHom f (𝟙 Z) g (𝟙 Z)).trans
        (congrArg (fun h : Z ⟶ Z => (f ≫ g) ⊗ₘ h) (Category.id_comp (𝟙 Z)))
    _ = (tensorRight Z).map (f ≫ g) := tensorHom_id (f ≫ g) Z

/-- The actual native freely based discrete object smashed with the coefficient. -/
abbrev discreteSmashObj (I : Type w) (Z : PointedCGWH.{u, max v w}) :
    PointedCGWH.{u, max v w} :=
  basedDiscreteObj.{u, v, w} I ⊗ Z

/-- The coefficient generator uses the actual left unitor and based point inclusion. -/
def discreteSmashIncl (I : Type w) (Z : PointedCGWH.{u, max v w}) (i : I) :
    Z ⟶ discreteSmashObj.{u, v, w} I Z :=
  (λ_ Z).inv ≫ (basedDiscreteIncl.{u, v, w} I i ⊗ₘ 𝟙 Z)

/-- The literal public generator is transported through the actual free-point unit. -/
private theorem discreteSmashIncl_unitTransport (I : Type w)
    (Z : PointedCGWH.{u, max v w}) (i : I) :
    discreteSmashIncl.{u, v, w} I Z i =
      (nativeCoefficientUnitIso.{u, max v w} Z).inv ≫
        (tensorRight Z).map (basedDiscreteIncl.{u, v, w} I i) := by
  let U : PointedCGWH.{u, max v w} :=
    (Under.costar CGWH.point.{u, max v w}).obj CGWH.point
  have hunit : (nativeCoefficientUnitIso.{u, max v w} Z).inv = (λ_ Z).inv := by
    change (λ_ Z).inv ≫ (tensorRight Z).map (𝟙 U) = (λ_ Z).inv
    exact (congrArg
      (fun f : (tensorRight Z).obj U ⟶ (tensorRight Z).obj U => (λ_ Z).inv ≫ f)
      ((tensorRight Z).map_id U)).trans (Category.comp_id (λ_ Z).inv)
  calc
    discreteSmashIncl.{u, v, w} I Z i =
        (λ_ Z).inv ≫ (tensorRight Z).map (basedDiscreteIncl.{u, v, w} I i) :=
      congrArg
        (fun f : U ⊗ Z ⟶ basedDiscreteObj.{u, v, w} I ⊗ Z => (λ_ Z).inv ≫ f)
        (tensorHom_id (basedDiscreteIncl.{u, v, w} I i) Z)
    _ = (nativeCoefficientUnitIso.{u, max v w} Z).inv ≫
        (tensorRight Z).map (basedDiscreteIncl.{u, v, w} I i) :=
      congrArg
        (fun f : Z ⟶ (tensorRight Z).obj U =>
          f ≫ (tensorRight Z).map (basedDiscreteIncl.{u, v, w} I i)) hunit.symm

/-- The literal native coefficient generators form a constant coefficient cofan. -/
def discreteSmashCofan (I : Type w) (Z : PointedCGWH.{u, max v w}) :
    Cofan (fun _ : I => Z) :=
  Cofan.mk (discreteSmashObj.{u, v, w} I Z) (discreteSmashIncl I Z)

/-- Fixed-right smash preserves the actual based point coproduct; unit transport
makes its components the original coefficient, rather than unit smash coefficient. -/
def discreteSmashCofanIsColimit (I : Type w)
    (Z : PointedCGWH.{u, max v w}) :
    IsColimit (discreteSmashCofan.{u, v, w} I Z) := by
  let R : PointedCGWH.{u, max v w} ⥤ PointedCGWH.{u, max v w} :=
    tensorRight Z
  let U : PointedCGWH.{u, max v w} :=
    (Under.costar CGWH.point.{u, max v w}).obj CGWH.point
  let c := basedDiscreteCofan.{u, v, w} I
  let e := λ_ Z
  have htransport (i : I) : discreteSmashIncl.{u, v, w} I Z i =
      e.inv ≫ R.map (basedDiscreteIncl.{u, v, w} I i) :=
    congrArg
      (fun f : U ⊗ Z ⟶ basedDiscreteObj.{u, v, w} I ⊗ Z => e.inv ≫ f)
      (tensorHom_id (basedDiscreteIncl.{u, v, w} I i) Z)
  have hc : IsColimit
      (Cofan.mk (R.obj (basedDiscreteObj.{u, v, w} I))
        (fun i => R.map (basedDiscreteIncl.{u, v, w} I i))) :=
    (Cofan.isColimitMapCoconeEquiv R
      (fun _ : I => (Under.costar CGWH.point.{u, max v w}).obj CGWH.point) c)
      (isColimitOfPreserves R (basedDiscreteCofanIsColimit.{u, v, w} I))
  let lift (s : Cofan (fun _ : I => Z)) :
      discreteSmashObj.{u, v, w} I Z ⟶ s.pt :=
    hc.desc (Cofan.mk s.pt (fun i => e.hom ≫ s.inj i))
  refine Cofan.IsColimit.mk _ lift ?_ ?_
  · intro s i
    change discreteSmashIncl.{u, v, w} I Z i ≫ lift s = s.inj i
    rw [htransport, Category.assoc]
    change e.inv ≫ R.map (basedDiscreteIncl.{u, v, w} I i) ≫
      hc.desc (Cofan.mk s.pt (fun i => e.hom ≫ s.inj i)) = s.inj i
    have hfac : R.map (basedDiscreteIncl.{u, v, w} I i) ≫
        hc.desc (Cofan.mk s.pt (fun i => e.hom ≫ s.inj i)) =
        e.hom ≫ s.inj i :=
      hc.fac (Cofan.mk s.pt (fun i => e.hom ≫ s.inj i)) ⟨i⟩
    calc
      _ = e.inv ≫ (e.hom ≫ s.inj i) :=
        congrArg (fun f : R.obj U ⟶ s.pt => e.inv ≫ f) hfac
      _ = s.inj i := by rw [Iso.inv_hom_id_assoc]
  · intro s m hm
    let m' : discreteSmashObj.{u, v, w} I Z ⟶ s.pt := m
    have hm' : ∀ i, discreteSmashIncl.{u, v, w} I Z i ≫ m' = s.inj i := hm
    change m' = lift s
    apply hc.hom_ext
    intro j
    have h := congrArg (fun f : Z ⟶ s.pt => e.hom ≫ f) (hm' j.as)
    rw [htransport, Category.assoc, Iso.hom_inv_id_assoc] at h
    have hfac : R.map (basedDiscreteIncl.{u, v, w} I j.as) ≫
        hc.desc (Cofan.mk s.pt (fun i => e.hom ≫ s.inj i)) =
        e.hom ≫ s.inj j.as :=
      hc.fac (Cofan.mk s.pt (fun i => e.hom ≫ s.inj i)) j
    change R.map (basedDiscreteIncl.{u, v, w} I j.as) ≫ m' =
      R.map (basedDiscreteIncl.{u, v, w} I j.as) ≫
        hc.desc (Cofan.mk s.pt (fun i => e.hom ≫ s.inj i))
    exact h.trans hfac.symm

/-- The actual native cofan constructs coefficient-coproduct existence. -/
theorem discreteSmashHasCoproduct (I : Type w)
    (Z : PointedCGWH.{u, max v w}) :
    HasCoproduct (fun _ : I => Z) :=
  HasColimit.mk ⟨discreteSmashCofan I Z, discreteSmashCofanIsColimit I Z⟩

/-- Compare with the original selected coefficient coproduct dictionary. -/
def discreteSmashCoproductIso (I : Type w)
    (Z : PointedCGWH.{u, max v w}) [HasCoproduct (fun _ : I => Z)] :
    discreteSmashObj.{u, v, w} I Z ≅ ∐ fun _ : I => Z :=
  (discreteSmashCofanIsColimit I Z).coconePointUniqueUpToIso
    (coproductIsCoproduct (fun _ : I => Z))

@[reassoc (attr := simp)]
theorem discreteSmashCoproductIso_generator (I : Type w)
    (Z : PointedCGWH.{u, max v w}) [HasCoproduct (fun _ : I => Z)] (i : I) :
    discreteSmashIncl.{u, v, w} I Z i ≫ (discreteSmashCoproductIso I Z).hom =
      Sigma.ι (fun _ : I => Z) i :=
  (discreteSmashCofanIsColimit I Z).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct (fun _ : I => Z)) ⟨i⟩

/-- The actual native coefficient cofan supplies descent for arbitrary legs. -/
def discreteSmashDesc (I : Type w) (Z : PointedCGWH.{u, max v w})
    {Y : PointedCGWH.{u, max v w}} (f : I → (Z ⟶ Y)) :
    discreteSmashObj.{u, v, w} I Z ⟶ Y :=
  (discreteSmashCofanIsColimit I Z).desc (Cofan.mk Y f)

@[reassoc (attr := simp)]
theorem discreteSmashDesc_generator (I : Type w)
    (Z : PointedCGWH.{u, max v w})
    {Y : PointedCGWH.{u, max v w}} (f : I → (Z ⟶ Y)) (i : I) :
    discreteSmashIncl.{u, v, w} I Z i ≫ discreteSmashDesc I Z f = f i :=
  (discreteSmashCofanIsColimit I Z).fac (Cofan.mk Y f) ⟨i⟩

/-- Maps out of the actual native smash are determined by its coefficient generators. -/
@[ext]
theorem discreteSmash_hom_ext (I : Type w) (Z : PointedCGWH.{u, max v w})
    {Y : PointedCGWH.{u, max v w}}
    {f g : discreteSmashObj.{u, v, w} I Z ⟶ Y}
    (h : ∀ i, discreteSmashIncl I Z i ≫ f = discreteSmashIncl I Z i ≫ g) :
    f = g :=
  (discreteSmashCofanIsColimit I Z).hom_ext (fun ⟨i⟩ => h i)

/-- Full left multiplication on the actual native coefficient smash. -/
def discreteSmashLeft (G : Type w) [Group G]
    (Z : PointedCGWH.{u, max v w}) (k : G) :
    discreteSmashObj.{u, v, w} G Z ⟶ discreteSmashObj G Z :=
  (leftTranslationAut.{u, v, w} G k).asIso.hom ⊗ₘ 𝟙 Z

@[reassoc (attr := simp)]
theorem discreteSmashLeft_generator (G : Type w) [Group G]
    (Z : PointedCGWH.{u, max v w}) (k g : G) :
    discreteSmashIncl.{u, v, w} G Z g ≫ discreteSmashLeft G Z k =
      discreteSmashIncl G Z (k * g) := by
  rw [discreteSmashIncl_unitTransport.{u, v, w}, Category.assoc]
  change (nativeCoefficientUnitIso.{u, max v w} Z).inv ≫
    (tensorRight Z).map (basedDiscreteIncl.{u, v, w} G g) ≫
      ((leftTranslationAut.{u, v, w} G k).asIso.hom ⊗ₘ 𝟙 Z) =
    discreteSmashIncl.{u, v, w} G Z (k * g)
  rw [nativeTensorRight_comp, leftTranslationAut_generator.{u, v, w}]
  exact (discreteSmashIncl_unitTransport.{u, v, w} G Z (k * g)).symm

section Balancing

variable (H : Type wH) (G : Type wG) [Monoid H] [Group G]
variable (Z : PointedCGWH.{u, max v (max wH wG)})
variable (rho : H →* End Z) (iota : H →* G)

/-- The cross-universe native group map is the actual point-cofan descender. -/
def balancingIndexMap :
    basedDiscreteObj.{u, max v (max wH wG), max wG wH} (G × H) ⟶
      basedDiscreteObj.{u, max v (max wH wG), wG} G :=
  (Under.costar CGWH.point.{u, max v (max wH wG)}).map
    (CGWH.discreteCofanDesc.{u, max v (max wH wG), max wG wH} (G × H)
      (Cofan.mk (CGWH.discreteObj.{u, max v (max wH wG), wG} G)
        (fun ga => CGWH.discreteObjIncl.{u, max v (max wH wG), wG} G (ga.1 * iota ga.2))))

@[reassoc (attr := simp)]
theorem balancingIndexMap_generator (ga : G × H) :
    basedDiscreteIncl.{u, max v (max wH wG), max wG wH} (G × H) ga ≫
        balancingIndexMap.{u, v, wH, wG} H G iota =
      basedDiscreteIncl.{u, max v (max wH wG), wG} G (ga.1 * iota ga.2) := by
  let F := Under.costar CGWH.point.{u, max v (max wH wG)}
  let d := CGWH.discreteCofanDesc.{u, max v (max wH wG), max wG wH} (G × H)
    (Cofan.mk (CGWH.discreteObj.{u, max v (max wH wG), wG} G)
      (fun ga => CGWH.discreteObjIncl.{u, max v (max wH wG), wG}
        G (ga.1 * iota ga.2)))
  have hfac :
      CGWH.discreteObjIncl.{u, max v (max wH wG), max wG wH} (G × H) ga ≫ d =
        CGWH.discreteObjIncl.{u, max v (max wH wG), wG} G (ga.1 * iota ga.2) :=
    (CGWH.discreteCofanIsColimit.{u, max v (max wH wG), max wG wH} (G × H)).fac
      (Cofan.mk (CGWH.discreteObj.{u, max v (max wH wG), wG} G)
        (fun ga => CGWH.discreteObjIncl.{u, max v (max wH wG), wG}
          G (ga.1 * iota ga.2))) ⟨ga⟩
  change F.map
      (CGWH.discreteObjIncl.{u, max v (max wH wG), max wG wH} (G × H) ga) ≫
        F.map d =
      F.map (CGWH.discreteObjIncl.{u, max v (max wH wG), wG} G (ga.1 * iota ga.2))
  exact (F.map_comp
      (CGWH.discreteObjIncl.{u, max v (max wH wG), max wG wH} (G × H) ga) d).symm.trans
    (congrArg
      (fun f : CGWH.point.{u, max v (max wH wG)} ⟶
        CGWH.discreteObj.{u, max v (max wH wG), wG} G => F.map f) hfac)

/-- The actual group balancing arrow smashes the actual native group map with identity. -/
def smashBalancingGroup :
    discreteSmashObj.{u, max v (max wH wG), max wG wH} (G × H) Z ⟶
      discreteSmashObj.{u, max v (max wH wG), wG} G Z :=
  balancingIndexMap.{u, v, wH, wG} H G iota ⊗ₘ 𝟙 Z

@[reassoc (attr := simp)]
theorem smashBalancingGroup_generator (ga : G × H) :
    discreteSmashIncl.{u, max v (max wH wG), max wG wH} (G × H) Z ga ≫
        smashBalancingGroup.{u, v, wH, wG} H G Z iota =
      discreteSmashIncl.{u, max v (max wH wG), wG} G Z (ga.1 * iota ga.2) := by
  rw [discreteSmashIncl_unitTransport.{u, max v (max wH wG), max wG wH},
    Category.assoc]
  change (nativeCoefficientUnitIso.{u, max v (max wH wG)} Z).inv ≫
    (tensorRight Z).map
      (basedDiscreteIncl.{u, max v (max wH wG), max wG wH} (G × H) ga) ≫
      (balancingIndexMap.{u, v, wH, wG} H G iota ⊗ₘ 𝟙 Z) =
    discreteSmashIncl.{u, max v (max wH wG), wG} G Z (ga.1 * iota ga.2)
  rw [nativeTensorRight_comp, balancingIndexMap_generator.{u, v, wH, wG} H G iota ga]
  exact (discreteSmashIncl_unitTransport.{u, max v (max wH wG), wG}
    G Z (ga.1 * iota ga.2)).symm

/-- The coefficient balancing arrow uses actual End coefficients on the actual source cofan. -/
def smashBalancingCoefficient :
    discreteSmashObj.{u, max v (max wH wG), max wG wH} (G × H) Z ⟶
      discreteSmashObj.{u, max v (max wH wG), wG} G Z :=
  discreteSmashDesc.{u, max v (max wH wG), max wG wH} (G × H) Z
    (fun ga => End.asHom (rho ga.2) ≫ discreteSmashIncl.{u, max v (max wH wG), wG} G Z ga.1)

omit [Group G] in
@[reassoc (attr := simp)]
theorem smashBalancingCoefficient_generator (ga : G × H) :
    discreteSmashIncl.{u, max v (max wH wG), max wG wH} (G × H) Z ga ≫
        smashBalancingCoefficient.{u, v, wH, wG} H G Z rho =
      End.asHom (rho ga.2) ≫ discreteSmashIncl.{u, max v (max wH wG), wG} G Z ga.1 :=
  discreteSmashDesc_generator.{u, max v (max wH wG), max wG wH} (G × H) Z _ ga

/-- The actual source permutation sends (g,a) to (k*g,a), keeping the coefficient label. -/
def smashBalancingSourceLeft (k : G) :
    discreteSmashObj.{u, max v (max wH wG), max wG wH} (G × H) Z ⟶
      discreteSmashObj.{u, max v (max wH wG), max wG wH} (G × H) Z :=
  (permutationAut.{u, max v (max wH wG), max wG wH} (G × H)
    (Equiv.prodCongr (Equiv.mulLeft k) (Equiv.refl H))).asIso.hom ⊗ₘ 𝟙 Z

omit [Monoid H] in
@[reassoc (attr := simp)]
theorem smashBalancingSourceLeft_generator (k : G) (ga : G × H) :
    discreteSmashIncl.{u, max v (max wH wG), max wG wH} (G × H) Z ga ≫
        smashBalancingSourceLeft.{u, v, wH, wG} H G Z k =
      discreteSmashIncl.{u, max v (max wH wG), max wG wH} (G × H) Z (k * ga.1, ga.2) := by
  rw [discreteSmashIncl_unitTransport.{u, max v (max wH wG), max wG wH},
    Category.assoc]
  change (nativeCoefficientUnitIso.{u, max v (max wH wG)} Z).inv ≫
    (tensorRight Z).map
      (basedDiscreteIncl.{u, max v (max wH wG), max wG wH} (G × H) ga) ≫
      ((permutationAut.{u, max v (max wH wG), max wG wH} (G × H)
        (Equiv.prodCongr (Equiv.mulLeft k) (Equiv.refl H))).asIso.hom ⊗ₘ 𝟙 Z) =
    discreteSmashIncl.{u, max v (max wH wG), max wG wH}
      (G × H) Z (k * ga.1, ga.2)
  rw [nativeTensorRight_comp,
    permutationAut_generator.{u, max v (max wH wG), max wG wH}]
  exact (discreteSmashIncl_unitTransport.{u, max v (max wH wG), max wG wH}
    (G × H) Z (k * ga.1, ga.2)).symm

/-- Full native left multiplication commutes with the actual group balancing arrow. -/
theorem smashBalancingGroup_left (k : G) :
    smashBalancingSourceLeft.{u, v, wH, wG} H G Z k ≫ smashBalancingGroup.{u, v, wH, wG} H G Z iota
        =
      smashBalancingGroup.{u, v, wH, wG} H G Z iota ≫
        discreteSmashLeft.{u, max v (max wH wG), wG} G Z k := by
  apply discreteSmash_hom_ext.{u, max v (max wH wG), max wG wH} (G × H) Z
  intro ga
  rw [← Category.assoc, smashBalancingSourceLeft_generator.{u, v, wH, wG} H G Z,
    smashBalancingGroup_generator.{u, v, wH, wG} H G Z iota, ← Category.assoc,
    smashBalancingGroup_generator.{u, v, wH, wG} H G Z iota, discreteSmashLeft_generator.{u, max v
        (max wH wG), wG}]
  rw [mul_assoc]

/-- The same full left multiplication commutes with the actual End coefficient arrow. -/
theorem smashBalancingCoefficient_left (k : G) :
    smashBalancingSourceLeft.{u, v, wH, wG} H G Z k ≫ smashBalancingCoefficient.{u, v, wH, wG} H G
        Z rho =
      smashBalancingCoefficient.{u, v, wH, wG} H G Z rho ≫
        discreteSmashLeft.{u, max v (max wH wG), wG} G Z k := by
  apply discreteSmash_hom_ext.{u, max v (max wH wG), max wG wH} (G × H) Z
  intro ga
  rw [← Category.assoc, smashBalancingSourceLeft_generator.{u, v, wH, wG} H G Z,
    smashBalancingCoefficient_generator.{u, v, wH, wG} H G Z rho, ← Category.assoc,
    smashBalancingCoefficient_generator.{u, v, wH, wG} H G Z rho, Category.assoc,
    discreteSmashLeft_generator.{u, max v (max wH wG), wG}]

variable [HasCoproduct (fun _ : G => Z)] [HasCoproduct (fun _ : G × H => Z)]

/-- The source/target native comparisons identify the actual group arrow. -/
theorem smashBalancingGroup_comparison :
    (discreteSmashCoproductIso.{u, max v (max wH wG), max wG wH} (G × H) Z).hom ≫
        ActionCategory.balancedGroupArrow H G Z iota =
      smashBalancingGroup.{u, v, wH, wG} H G Z iota ≫ (discreteSmashCoproductIso.{u, max v (max wH
          wG), wG} G Z).hom := by
  apply discreteSmash_hom_ext.{u, max v (max wH wG), max wG wH} (G × H) Z
  intro ga
  rw [← Category.assoc, discreteSmashCoproductIso_generator.{u, max v (max wH wG), max wG wH} (G ×
      H) Z]
  simp only [ActionCategory.balancedGroupArrow, Sigma.ι_comp_desc]
  rw [← Category.assoc, smashBalancingGroup_generator.{u, v, wH, wG} H G Z iota,
    discreteSmashCoproductIso_generator.{u, max v (max wH wG), wG} G Z]

omit [Group G] in
/-- The same comparisons retain the actual End coefficient arrow. -/
theorem smashBalancingCoefficient_comparison :
    (discreteSmashCoproductIso.{u, max v (max wH wG), max wG wH} (G × H) Z).hom ≫
        ActionCategory.balancedCoefficientArrow H G Z rho =
      smashBalancingCoefficient.{u, v, wH, wG} H G Z rho ≫ (discreteSmashCoproductIso.{u, max v
          (max wH wG), wG} G Z).hom := by
  apply discreteSmash_hom_ext.{u, max v (max wH wG), max wG wH} (G × H) Z
  intro ga
  rw [← Category.assoc, discreteSmashCoproductIso_generator.{u, max v (max wH wG), max wG wH} (G ×
      H) Z]
  simp only [ActionCategory.balancedCoefficientArrow, Sigma.ι_comp_desc]
  rw [← Category.assoc, smashBalancingCoefficient_generator.{u, v, wH, wG} H G Z rho,
    Category.assoc, discreteSmashCoproductIso_generator.{u, max v (max wH wG), wG} G Z]

end Balancing
end PointedCGWH
