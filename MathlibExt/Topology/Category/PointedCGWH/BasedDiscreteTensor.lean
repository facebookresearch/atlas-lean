/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.DiscreteSmash

/-!
# Smash products of based discrete spaces

Constructs the isomorphism between the smash product of two based discrete spaces and the based discrete space on their Cartesian product. Both maps are specified on point-pair generators; the tensor unit is compared with the based discrete singleton.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace PointedCGWH

/-- One actual based point coproduct is the selected native smash unit. -/
def basedDiscreteUnitIso :
    𝟙_ PointedCGWH.{u, max v w} ≅ basedDiscreteObj.{u, v, w} PUnit.{w + 1} := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let hc := basedDiscreteCofanIsColimit.{u, v, w} PUnit.{w + 1}
  let epsilon : U ⟶ basedDiscreteObj.{u, v, w} PUnit.{w + 1} :=
    basedDiscreteIncl.{u, v, w} PUnit.{w + 1} PUnit.unit
  let eta : basedDiscreteObj.{u, v, w} PUnit.{w + 1} ⟶ U :=
    hc.desc (Cofan.mk U (fun _ => 𝟙 U))
  have hfac : epsilon ≫ eta = 𝟙 U :=
    hc.fac (Cofan.mk U (fun _ => 𝟙 U)) ⟨PUnit.unit⟩
  refine { hom := epsilon, inv := eta, hom_inv_id := hfac, inv_hom_id := ?_ }
  apply Cofan.IsColimit.hom_ext hc
  intro p
  cases p
  change epsilon ≫ (eta ≫ epsilon) = epsilon ≫ 𝟙 _
  exact (Category.assoc epsilon eta epsilon).symm.trans
    ((congrArg (fun f : U ⟶ U => f ≫ epsilon) hfac).trans
      ((Category.id_comp epsilon).trans (Category.comp_id epsilon).symm))

/-- The literal pair generator uses the actual native left unitor and two point injections. -/
def basedDiscretePairIncl (E F : Type w) (e : E) (f : F) :
    𝟙_ PointedCGWH.{u, max v w} ⟶
      basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F :=
  (λ_ (𝟙_ PointedCGWH.{u, max v w})).inv ≫
    (basedDiscreteIncl.{u, v, w} E e ⊗ₘ basedDiscreteIncl.{u, v, w} F f)

/-- The pair generator is exactly the two successive existing coefficient generators. -/
theorem basedDiscretePairIncl_eq (E F : Type w) (e : E) (f : F) :
    basedDiscretePairIncl.{u, v, w} E F e f =
      basedDiscreteIncl.{u, v, w} F f ≫
        discreteSmashIncl.{u, v, w} E (basedDiscreteObj.{u, v, w} F) e := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let iE : U ⟶ basedDiscreteObj.{u, v, w} E := basedDiscreteIncl.{u, v, w} E e
  let iF : U ⟶ basedDiscreteObj.{u, v, w} F := basedDiscreteIncl.{u, v, w} F f
  have htensor :
      (𝟙 U ⊗ₘ iF) ≫ (iE ⊗ₘ 𝟙 (basedDiscreteObj.{u, v, w} F)) = iE ⊗ₘ iF :=
    (tensorHom_comp_tensorHom (𝟙 U) iF iE (𝟙 (basedDiscreteObj.{u, v, w} F))).trans
      (congrArg₂ (fun a b => a ⊗ₘ b) (Category.id_comp iE) (Category.comp_id iF))
  have hunit : (λ_ U).inv ≫ (𝟙 U ⊗ₘ iF) =
      iF ≫ (λ_ (basedDiscreteObj.{u, v, w} F)).inv :=
    (congrArg (fun a => (λ_ U).inv ≫ a) (id_tensorHom U iF)).trans
      (leftUnitor_inv_naturality iF).symm
  change (λ_ U).inv ≫ (iE ⊗ₘ iF) =
    iF ≫ ((λ_ (basedDiscreteObj.{u, v, w} F)).inv ≫
      (iE ⊗ₘ 𝟙 (basedDiscreteObj.{u, v, w} F)))
  calc
    _ = (λ_ U).inv ≫
        ((𝟙 U ⊗ₘ iF) ≫ (iE ⊗ₘ 𝟙 (basedDiscreteObj.{u, v, w} F))) :=
      congrArg (fun a => (λ_ U).inv ≫ a) htensor.symm
    _ = ((λ_ U).inv ≫ (𝟙 U ⊗ₘ iF)) ≫
        (iE ⊗ₘ 𝟙 (basedDiscreteObj.{u, v, w} F)) := (Category.assoc _ _ _).symm
    _ = (iF ≫ (λ_ (basedDiscreteObj.{u, v, w} F)).inv) ≫
        (iE ⊗ₘ 𝟙 (basedDiscreteObj.{u, v, w} F)) :=
      congrArg (fun a => a ≫ (iE ⊗ₘ 𝟙 (basedDiscreteObj.{u, v, w} F))) hunit
    _ = _ := Category.assoc _ _ _

/-- The actual tensor-to-product map descends the existing coefficient cofan. -/
def basedDiscreteTensorProductHom (E F : Type w) :
    basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F ⟶
      basedDiscreteObj.{u, v, w} (E × F) :=
  discreteSmashDesc.{u, v, w} E (basedDiscreteObj.{u, v, w} F)
    (fun e => basedDiscreteFunctor.{u, v, w}.map (↾fun f : F => (e, f)))

/-- The inverse product-to-tensor map descends the actual product-index point cofan. -/
def basedDiscreteTensorProductInv (E F : Type w) :
    basedDiscreteObj.{u, v, w} (E × F) ⟶
      basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F :=
  (basedDiscreteCofanIsColimit.{u, v, w} (E × F)).desc
    (Cofan.mk _ (fun p => basedDiscretePairIncl.{u, v, w} E F p.1 p.2))

/-- The tensor-to-product map sends the literal pair generator to the literal pair injection. -/
theorem basedDiscreteTensorProductHom_pair (E F : Type w) (e : E) (f : F) :
    basedDiscretePairIncl.{u, v, w} E F e f ≫
        basedDiscreteTensorProductHom.{u, v, w} E F =
      basedDiscreteIncl.{u, v, w} (E × F) (e, f) := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let XF : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} F
  let T : PointedCGWH.{u, max v w} :=
    basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F
  let EF : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (E × F)
  let iF : U ⟶ XF := basedDiscreteIncl.{u, v, w} F f
  let j : XF ⟶ T := discreteSmashIncl.{u, v, w} E XF e
  let m : T ⟶ EF := basedDiscreteTensorProductHom.{u, v, w} E F
  let p : U ⟶ T := basedDiscretePairIncl.{u, v, w} E F e f
  let a : XF ⟶ EF := basedDiscreteFunctor.{u, v, w}.map (↾fun f : F => (e, f))
  let iEF : U ⟶ EF := basedDiscreteIncl.{u, v, w} (E × F) (e, f)
  have hp : p = iF ≫ j := basedDiscretePairIncl_eq.{u, v, w} E F e f
  have hfac : j ≫ m = a :=
    discreteSmashDesc_generator.{u, v, w} E XF _ e
  have hNatural : iF ≫ a = iEF :=
    basedDiscreteIncl_naturality.{u, v, w} (fun f : F => (e, f)) f
  have hStart : p ≫ m = (iF ≫ j) ≫ m :=
    congrArg (fun b : U ⟶ T => b ≫ m) hp
  have hMiddle : iF ≫ (j ≫ m) = iF ≫ a :=
    congrArg (fun b : XF ⟶ EF => iF ≫ b) hfac
  change p ≫ m = iEF
  exact hStart.trans ((Category.assoc iF j m).trans (hMiddle.trans hNatural))

/-- The product-to-tensor map keeps the literal pair generator. -/
theorem basedDiscreteTensorProductInv_pair (E F : Type w) (e : E) (f : F) :
    basedDiscreteIncl.{u, v, w} (E × F) (e, f) ≫
        basedDiscreteTensorProductInv.{u, v, w} E F =
      basedDiscretePairIncl.{u, v, w} E F e f :=
  (basedDiscreteCofanIsColimit.{u, v, w} (E × F)).fac
    (Cofan.mk _ (fun p => basedDiscretePairIncl.{u, v, w} E F p.1 p.2)) ⟨(e, f)⟩

/-- The actual unit copowers carry the tensor/product comparison needed by Gamma. -/
def basedDiscreteTensorProductIso (E F : Type w) :
    basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F ≅
      basedDiscreteObj.{u, v, w} (E × F) where
  hom := basedDiscreteTensorProductHom.{u, v, w} E F
  inv := basedDiscreteTensorProductInv.{u, v, w} E F
  hom_inv_id := by
    apply discreteSmash_hom_ext.{u, v, w} E (basedDiscreteObj.{u, v, w} F)
    intro e
    apply Cofan.IsColimit.hom_ext (basedDiscreteCofanIsColimit.{u, v, w} F)
    intro f
    let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
    let XF : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} F
    let T : PointedCGWH.{u, max v w} :=
      basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F
    let EF : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (E × F)
    let iF : U ⟶ XF := basedDiscreteIncl.{u, v, w} F f
    let j : XF ⟶ T := discreteSmashIncl.{u, v, w} E XF e
    let m : T ⟶ EF := basedDiscreteTensorProductHom.{u, v, w} E F
    let n : EF ⟶ T := basedDiscreteTensorProductInv.{u, v, w} E F
    let p : U ⟶ T := basedDiscretePairIncl.{u, v, w} E F e f
    let iEF : U ⟶ EF := basedDiscreteIncl.{u, v, w} (E × F) (e, f)
    have hp : p = iF ≫ j := basedDiscretePairIncl_eq.{u, v, w} E F e f
    have hm : p ≫ m = iEF := basedDiscreteTensorProductHom_pair.{u, v, w} E F e f
    have hn : iEF ≫ n = p := basedDiscreteTensorProductInv_pair.{u, v, w} E F e f
    have hStart : iF ≫ (j ≫ (m ≫ n)) = p ≫ (m ≫ n) :=
      (Category.assoc iF j (m ≫ n)).symm.trans
        (congrArg (fun b : U ⟶ T => b ≫ (m ≫ n)) hp.symm)
    have hRound : p ≫ (m ≫ n) = p :=
      (Category.assoc p m n).symm.trans
        ((congrArg (fun b : U ⟶ EF => b ≫ n) hm).trans hn)
    have hLast : p = iF ≫ (j ≫ 𝟙 T) :=
      hp.trans (congrArg (fun b : XF ⟶ T => iF ≫ b) (Category.comp_id j).symm)
    change iF ≫ (j ≫ (m ≫ n)) = iF ≫ (j ≫ 𝟙 T)
    exact hStart.trans (hRound.trans hLast)
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext (basedDiscreteCofanIsColimit.{u, v, w} (E × F))
    rintro ⟨e, f⟩
    let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
    let T : PointedCGWH.{u, max v w} :=
      basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F
    let EF : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (E × F)
    let iEF : U ⟶ EF := basedDiscreteIncl.{u, v, w} (E × F) (e, f)
    let p : U ⟶ T := basedDiscretePairIncl.{u, v, w} E F e f
    let m : T ⟶ EF := basedDiscreteTensorProductHom.{u, v, w} E F
    let n : EF ⟶ T := basedDiscreteTensorProductInv.{u, v, w} E F
    have hn : iEF ≫ n = p := basedDiscreteTensorProductInv_pair.{u, v, w} E F e f
    have hm : p ≫ m = iEF := basedDiscreteTensorProductHom_pair.{u, v, w} E F e f
    have hRound : iEF ≫ (n ≫ m) = iEF :=
      (Category.assoc iEF n m).symm.trans
        ((congrArg (fun b : U ⟶ T => b ≫ m) hn).trans hm)
    change iEF ≫ (n ≫ m) = iEF ≫ 𝟙 EF
    exact hRound.trans (Category.comp_id iEF).symm

end PointedCGWH
