/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Action.Coinvariants

/-!
# Equivariant transport of coefficient indices

An equivariant index map acts on the actual chosen coefficient colimits.
An equivariant bijection gives an isomorphism with literal generator laws.
-/

set_option autoImplicit false
noncomputable section

universe u v wH wE wF wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ActionCategory

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) [Monoid H]
variable (E : Type wE) (F : Type wF) [MulAction H E] [MulAction H F]
variable (Z : C) (rho : H →* End Z)

/-- An equivariant index map transports actual coefficient-colimit legs. -/
def coefficientColimitIndexMap
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H F Z rho)]
    (t : E → F) (ht : ∀ (a : H) e, t (a • e) = a • t e) :
    colimit (coefficientDiagram H E Z rho) ⟶
      colimit (coefficientDiagram H F Z rho) :=
  colimit.desc (coefficientDiagram H E Z rho)
    (CoefficientFamily.cocone H E Z rho
      { leg := fun e => colimit.ι (coefficientDiagram H F Z rho) (t e : ActionCategory H F)
        relation := by
          intro a e
          rw [ht]
          exact colimit.w (coefficientDiagram H F Z rho)
            (show (t e : ActionCategory H F) ⟶
              ((a • t e : F) : ActionCategory H F) from ⟨a, rfl⟩) })

/-- The index map preserves the literal coefficient generator. -/
theorem coefficientColimitIndexMap_generator
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H F Z rho)]
    (t : E → F) (ht : ∀ (a : H) e, t (a • e) = a • t e) (e : E) :
    colimit.ι (coefficientDiagram H E Z rho) (e : ActionCategory H E) ≫
        coefficientColimitIndexMap H E F Z rho t ht =
      colimit.ι (coefficientDiagram H F Z rho) (t e : ActionCategory H F) :=
  colimit.ι_desc _ _

/-- The inverse of an equivariant bijection is equivariant. -/
theorem coefficientIndexEquiv_symm_smul
    (e : E ≃ F) (he : ∀ (a : H) x, e (a • x) = a • e x) (a : H) (x : F) :
    e.symm (a • x) = a • e.symm x := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- An equivariant bijection identifies the two actual chosen coefficient colimits. -/
def coefficientColimitIndexIso
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H F Z rho)]
    (e : E ≃ F) (he : ∀ (a : H) x, e (a • x) = a • e x) :
    colimit (coefficientDiagram H E Z rho) ≅
      colimit (coefficientDiagram H F Z rho) where
  hom := coefficientColimitIndexMap H E F Z rho e he
  inv := coefficientColimitIndexMap H F E Z rho e.symm
    (coefficientIndexEquiv_symm_smul H E F e he)
  hom_inv_id := by
    apply colimit.hom_ext
    intro x
    obtain ⟨i, rfl⟩ := (ActionCategory.objEquiv H E).surjective x
    let LE := colimit (coefficientDiagram H E Z rho)
    let LF := colimit (coefficientDiagram H F Z rho)
    let li : Z ⟶ LE := colimit.ι (coefficientDiagram H E Z rho) (i : ActionCategory H E)
    let lei : Z ⟶ LF := colimit.ι (coefficientDiagram H F Z rho) (e i : ActionCategory H F)
    let m : LE ⟶ LF := coefficientColimitIndexMap H E F Z rho e he
    let n : LF ⟶ LE := coefficientColimitIndexMap H F E Z rho e.symm
      (coefficientIndexEquiv_symm_smul H E F e he)
    have hm : li ≫ m = lei := coefficientColimitIndexMap_generator H E F Z rho e he i
    have hn : lei ≫ n = colimit.ι (coefficientDiagram H E Z rho)
        (e.symm (e i) : ActionCategory H E) :=
      coefficientColimitIndexMap_generator H F E Z rho e.symm
        (coefficientIndexEquiv_symm_smul H E F e he) (e i)
    have hlabel : colimit.ι (coefficientDiagram H E Z rho)
        (e.symm (e i) : ActionCategory H E) = li :=
      congrArg (fun j : E => (show Z ⟶ LE from
        colimit.ι (coefficientDiagram H E Z rho) (j : ActionCategory H E)))
        (e.symm_apply_apply i)
    have hcomp : (li ≫ m) ≫ n = li :=
      (congrArg (fun f : Z ⟶ LF => f ≫ n) hm).trans (hn.trans hlabel)
    change li ≫ (m ≫ n) = li ≫ 𝟙 LE
    exact (Category.assoc _ _ _).symm.trans (hcomp.trans (Category.comp_id li).symm)
  inv_hom_id := by
    apply colimit.hom_ext
    intro x
    obtain ⟨i, rfl⟩ := (ActionCategory.objEquiv H F).surjective x
    let LE := colimit (coefficientDiagram H E Z rho)
    let LF := colimit (coefficientDiagram H F Z rho)
    let li : Z ⟶ LF := colimit.ι (coefficientDiagram H F Z rho) (i : ActionCategory H F)
    let lei : Z ⟶ LE := colimit.ι (coefficientDiagram H E Z rho)
      (e.symm i : ActionCategory H E)
    let m : LF ⟶ LE := coefficientColimitIndexMap H F E Z rho e.symm
      (coefficientIndexEquiv_symm_smul H E F e he)
    let n : LE ⟶ LF := coefficientColimitIndexMap H E F Z rho e he
    have hm : li ≫ m = lei := coefficientColimitIndexMap_generator H F E Z rho e.symm
      (coefficientIndexEquiv_symm_smul H E F e he) i
    have hn : lei ≫ n = colimit.ι (coefficientDiagram H F Z rho)
        (e (e.symm i) : ActionCategory H F) :=
      coefficientColimitIndexMap_generator H E F Z rho e he (e.symm i)
    have hlabel : colimit.ι (coefficientDiagram H F Z rho)
        (e (e.symm i) : ActionCategory H F) = li :=
      congrArg (fun j : F => (show Z ⟶ LF from
        colimit.ι (coefficientDiagram H F Z rho) (j : ActionCategory H F)))
        (e.apply_symm_apply i)
    have hcomp : (li ≫ m) ≫ n = li :=
      (congrArg (fun f : Z ⟶ LE => f ≫ n) hm).trans (hn.trans hlabel)
    change li ≫ (m ≫ n) = li ≫ 𝟙 LF
    exact (Category.assoc _ _ _).symm.trans (hcomp.trans (Category.comp_id li).symm)

/-- Its forward comparison has the exact index generator characteristic. -/
theorem coefficientColimitIndexIso_generator
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H F Z rho)]
    (e : E ≃ F) (he : ∀ (a : H) x, e (a • x) = a • e x) (i : E) :
    colimit.ι (coefficientDiagram H E Z rho) (i : ActionCategory H E) ≫
        (coefficientColimitIndexIso H E F Z rho e he).hom =
      colimit.ι (coefficientDiagram H F Z rho) (e i : ActionCategory H F) :=
  coefficientColimitIndexMap_generator H E F Z rho e he i

/-- Its inverse comparison has the exact inverse-index generator characteristic. -/
theorem coefficientColimitIndexIso_inv_generator
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H F Z rho)]
    (e : E ≃ F) (he : ∀ (a : H) x, e (a • x) = a • e x) (i : F) :
    colimit.ι (coefficientDiagram H F Z rho) (i : ActionCategory H F) ≫
        (coefficientColimitIndexIso H E F Z rho e he).inv =
      colimit.ι (coefficientDiagram H E Z rho) (e.symm i : ActionCategory H E) :=
  coefficientColimitIndexMap_generator H F E Z rho e.symm
    (coefficientIndexEquiv_symm_smul H E F e he) i

/-- Index transport intertwines equivariant reindexing maps on both sides. -/
theorem coefficientColimitIndexMap_reindex
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H F Z rho)]
    (e : E → F) (he : ∀ (a : H) i, e (a • i) = a • e i)
    (t : E → E) (ht : ∀ (a : H) i, t (a • i) = a • t i)
    (s : F → F) (hs : ∀ (a : H) i, s (a • i) = a • s i)
    (hes : ∀ i, e (t i) = s (e i)) :
    coefficientColimitReindex H E Z rho t ht ≫
        coefficientColimitIndexMap H E F Z rho e he =
      coefficientColimitIndexMap H E F Z rho e he ≫
        coefficientColimitReindex H F Z rho s hs := by
  apply colimit.hom_ext
  intro x
  obtain ⟨i, rfl⟩ := (ActionCategory.objEquiv H E).surjective x
  let LE := colimit (coefficientDiagram H E Z rho)
  let LF := colimit (coefficientDiagram H F Z rho)
  let li : Z ⟶ LE := colimit.ι (coefficientDiagram H E Z rho) (i : ActionCategory H E)
  let lti : Z ⟶ LE := colimit.ι (coefficientDiagram H E Z rho) (t i : ActionCategory H E)
  let lei : Z ⟶ LF := colimit.ι (coefficientDiagram H F Z rho) (e i : ActionCategory H F)
  let lsei : Z ⟶ LF := colimit.ι (coefficientDiagram H F Z rho)
    (s (e i) : ActionCategory H F)
  let m : LE ⟶ LE := coefficientColimitReindex H E Z rho t ht
  let n : LF ⟶ LF := coefficientColimitReindex H F Z rho s hs
  let c : LE ⟶ LF := coefficientColimitIndexMap H E F Z rho e he
  have hm : li ≫ m = lti := coefficientColimitReindex_generator H E Z rho t ht i
  have hc : li ≫ c = lei := coefficientColimitIndexMap_generator H E F Z rho e he i
  have hct : lti ≫ c = colimit.ι (coefficientDiagram H F Z rho)
      (e (t i) : ActionCategory H F) :=
    coefficientColimitIndexMap_generator H E F Z rho e he (t i)
  have hn : lei ≫ n = lsei := coefficientColimitReindex_generator H F Z rho s hs (e i)
  have hlabel : colimit.ι (coefficientDiagram H F Z rho)
      (e (t i) : ActionCategory H F) = lsei :=
    congrArg (fun j : F => (show Z ⟶ LF from
      colimit.ι (coefficientDiagram H F Z rho) (j : ActionCategory H F))) (hes i)
  have hleft : (li ≫ m) ≫ c = lsei :=
    (congrArg (fun f : Z ⟶ LE => f ≫ c) hm).trans (hct.trans hlabel)
  have hright : (li ≫ c) ≫ n = lsei :=
    (congrArg (fun f : Z ⟶ LF => f ≫ n) hc).trans hn
  change li ≫ (m ≫ c) = li ≫ (c ≫ n)
  exact (Category.assoc _ _ _).symm.trans
    (hleft.trans (hright.symm.trans (Category.assoc _ _ _)))

/-- Index transport commutes with every equivariant coefficient map. -/
theorem coefficientColimitIndexMap_naturality
    (Z' : C) (rho' : H →* End Z') (f : Z ⟶ Z')
    (hf : ∀ a, (rho a).asHom ≫ f = f ≫ (rho' a).asHom)
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H F Z rho)]
    [HasColimit (coefficientDiagram H E Z' rho')]
    [HasColimit (coefficientDiagram H F Z' rho')]
    (t : E → F) (ht : ∀ (a : H) i, t (a • i) = a • t i) :
    colimMap (coefficientNatTrans H E Z Z' rho rho' f hf) ≫
        coefficientColimitIndexMap H E F Z' rho' t ht =
      coefficientColimitIndexMap H E F Z rho t ht ≫
        colimMap (coefficientNatTrans H F Z Z' rho rho' f hf) := by
  apply colimit.hom_ext
  intro x
  obtain ⟨i, rfl⟩ := (ActionCategory.objEquiv H E).surjective x
  let LE := colimit (coefficientDiagram H E Z rho)
  let LF := colimit (coefficientDiagram H F Z rho)
  let LE' := colimit (coefficientDiagram H E Z' rho')
  let LF' := colimit (coefficientDiagram H F Z' rho')
  let li : Z ⟶ LE := colimit.ι (coefficientDiagram H E Z rho) (i : ActionCategory H E)
  let lti : Z ⟶ LF := colimit.ι (coefficientDiagram H F Z rho) (t i : ActionCategory H F)
  let li' : Z' ⟶ LE' :=
    colimit.ι (coefficientDiagram H E Z' rho') (i : ActionCategory H E)
  let lti' : Z' ⟶ LF' :=
    colimit.ι (coefficientDiagram H F Z' rho') (t i : ActionCategory H F)
  let mE : LE ⟶ LE' := colimMap (coefficientNatTrans H E Z Z' rho rho' f hf)
  let mF : LF ⟶ LF' := colimMap (coefficientNatTrans H F Z Z' rho rho' f hf)
  let c : LE ⟶ LF := coefficientColimitIndexMap H E F Z rho t ht
  let c' : LE' ⟶ LF' := coefficientColimitIndexMap H E F Z' rho' t ht
  have hMapE : li ≫ mE = f ≫ li' :=
    ι_colimMap (coefficientNatTrans H E Z Z' rho rho' f hf) (i : ActionCategory H E)
  have hMapF : lti ≫ mF = f ≫ lti' :=
    ι_colimMap (coefficientNatTrans H F Z Z' rho rho' f hf) (t i : ActionCategory H F)
  have hIndex : li ≫ c = lti := coefficientColimitIndexMap_generator H E F Z rho t ht i
  have hIndex' : li' ≫ c' = lti' :=
    coefficientColimitIndexMap_generator H E F Z' rho' t ht i
  have hLeft : (li ≫ mE) ≫ c' = f ≫ lti' :=
    (congrArg (fun k : Z ⟶ LE' => k ≫ c') hMapE).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k : Z' ⟶ LF' => f ≫ k) hIndex'))
  have hRight : (li ≫ c) ≫ mF = f ≫ lti' :=
    (congrArg (fun k : Z ⟶ LF => k ≫ mF) hIndex).trans hMapF
  change li ≫ (mE ≫ c') = li ≫ (c ≫ mF)
  exact (Category.assoc _ _ _).symm.trans
    (hLeft.trans (hRight.symm.trans (Category.assoc _ _ _)))

/-- Transport along the literal identity index map is the identity of the chosen colimit. -/
theorem coefficientColimitIndexMap_id
    [HasColimit (coefficientDiagram H E Z rho)] :
    coefficientColimitIndexMap H E E Z rho id (fun _ _ => rfl) =
      𝟙 (colimit (coefficientDiagram H E Z rho)) := by
  apply colimit.hom_ext
  intro x
  obtain ⟨i, rfl⟩ := (ActionCategory.objEquiv H E).surjective x
  change colimit.ι (coefficientDiagram H E Z rho) (i : ActionCategory H E) ≫
      coefficientColimitIndexMap H E E Z rho id (fun _ _ => rfl) =
    colimit.ι (coefficientDiagram H E Z rho) (i : ActionCategory H E) ≫
      𝟙 (colimit (coefficientDiagram H E Z rho))
  exact (coefficientColimitIndexMap_generator H E E Z rho id
    (fun _ _ => rfl) i).trans (Category.comp_id _).symm

/-- Successive equivariant index transports compose on the literal chosen colimits. -/
theorem coefficientColimitIndexMap_comp
    (G : Type wG) [MulAction H G]
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H F Z rho)]
    [HasColimit (coefficientDiagram H G Z rho)]
    (t : E → F) (ht : ∀ (a : H) i, t (a • i) = a • t i)
    (s : F → G) (hs : ∀ (a : H) i, s (a • i) = a • s i) :
    coefficientColimitIndexMap H E F Z rho t ht ≫
        coefficientColimitIndexMap H F G Z rho s hs =
      coefficientColimitIndexMap H E G Z rho (s ∘ t)
        (fun a i => (congrArg s (ht a i)).trans (hs a (t i))) := by
  apply colimit.hom_ext
  intro x
  obtain ⟨i, rfl⟩ := (ActionCategory.objEquiv H E).surjective x
  let LE := colimit (coefficientDiagram H E Z rho)
  let LF := colimit (coefficientDiagram H F Z rho)
  let LG := colimit (coefficientDiagram H G Z rho)
  let li : Z ⟶ LE := colimit.ι (coefficientDiagram H E Z rho) (i : ActionCategory H E)
  let lti : Z ⟶ LF := colimit.ι (coefficientDiagram H F Z rho) (t i : ActionCategory H F)
  let lsti : Z ⟶ LG := colimit.ι (coefficientDiagram H G Z rho)
    (s (t i) : ActionCategory H G)
  let m : LE ⟶ LF := coefficientColimitIndexMap H E F Z rho t ht
  let n : LF ⟶ LG := coefficientColimitIndexMap H F G Z rho s hs
  let c : LE ⟶ LG := coefficientColimitIndexMap H E G Z rho (s ∘ t)
    (fun a i => (congrArg s (ht a i)).trans (hs a (t i)))
  have hm : li ≫ m = lti := coefficientColimitIndexMap_generator H E F Z rho t ht i
  have hn : lti ≫ n = lsti := coefficientColimitIndexMap_generator H F G Z rho s hs (t i)
  have hc : li ≫ c = lsti := coefficientColimitIndexMap_generator H E G Z rho (s ∘ t)
    (fun a i => (congrArg s (ht a i)).trans (hs a (t i))) i
  have hcomp : (li ≫ m) ≫ n = lsti :=
    (congrArg (fun f : Z ⟶ LF => f ≫ n) hm).trans hn
  change li ≫ (m ≫ n) = li ≫ c
  exact (Category.assoc _ _ _).symm.trans (hcomp.trans hc.symm)

end CategoryTheory.ActionCategory
