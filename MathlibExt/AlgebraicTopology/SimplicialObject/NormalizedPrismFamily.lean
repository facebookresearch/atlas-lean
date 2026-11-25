/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedChainHomotopy

/-!
# Naturality of a fixed original simplicial prism under a functor family

The original prism is chosen before the parameter varies. Each actual
family functor acts on that same prism. Native negative alternating sums,
Moore inclusion and native PInfty projection prove naturality of the
resulting normalized chain-homotopy components.

The source and parameter are arbitrary categories. The alternating result
needs only a preadditive target; Moore normalization needs an abelian target.
No additivity of the family functors, coefficient flatness, or desired
naturality certificate is assumed. Naturality when the original prism
itself varies is a separate statement.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicTopology
open scoped Simplicial

universe uC vC uD vD uI vI

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {I : Type uI} [Category.{vI} I]
  (F : I ⥤ (C ⥤ D))
  {X Y : SimplicialObject C} {f g : X ⟶ Y}
  (H : SimplicialObject.Homotopy f g)

section Alternating

variable [Preadditive D]

/-- The native alternating chain homotopies commute with every actual parameter map. -/
theorem alternatingFamilyHom_naturality {p q : I} (a : p ⟶ q) (n m : ℕ) :
    ((H.whiskerRight (F.obj p)).toChainHomotopy).hom n m ≫
        ((alternatingFaceMapComplex D).map (Functor.whiskerLeft Y (F.map a))).f m =
      ((alternatingFaceMapComplex D).map (Functor.whiskerLeft X (F.map a))).f n ≫
        ((H.whiskerRight (F.obj q)).toChainHomotopy).hom n m := by
  let τ := F.map a
  change ToChainHomotopy.hom (H.whiskerRight (F.obj p)) n m ≫ τ.app (Y.obj (op ⦋m⦌)) =
    τ.app (X.obj (op ⦋n⦌)) ≫ ToChainHomotopy.hom (H.whiskerRight (F.obj q)) n m
  by_cases h : n + 1 = m
  · subst m
    rw [ToChainHomotopy.hom_eq, ToChainHomotopy.hom_eq]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Preadditive.sum_comp,
      Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    exact congrArg (fun z => ((-1 : ℤ) ^ i.val) • z) (τ.naturality (H.h i))
  · rw [ToChainHomotopy.hom_eq_zero _ _ _ h,
      ToChainHomotopy.hom_eq_zero _ _ _ h, zero_comp, comp_zero]

end Alternating

section Normalized

variable [Abelian D]

/-- The existing normalized homotopy has exactly its native inclusion/homotopy/projection component. -/
theorem toNormalizedChainHomotopy_hom
    {Xd Yd : SimplicialObject D} {fd gd : Xd ⟶ Yd}
    (Hd : SimplicialObject.Homotopy fd gd) (n m : ℕ) :
    Hd.toNormalizedChainHomotopy.hom n m =
      (inclusionOfMooreComplexMap Xd).f n ≫ Hd.toChainHomotopy.hom n m ≫
        (DoldKan.PInftyToNormalizedMooreComplex Yd).f m := by
  let z : ((normalizedMooreComplex D).obj Xd).X n ⟶
      ((normalizedMooreComplex D).obj Yd).X m :=
    ((inclusionOfMooreComplexMap Xd).f n ≫ Hd.toChainHomotopy.hom n m) ≫
      (DoldKan.PInftyToNormalizedMooreComplex Yd).f m
  change (0 : ((normalizedMooreComplex D).obj Xd).X n ⟶
      ((normalizedMooreComplex D).obj Yd).X m) + (z + 0) = _
  have hZero : (0 : ((normalizedMooreComplex D).obj Xd).X n ⟶
      ((normalizedMooreComplex D).obj Yd).X m) + (z + 0) = z :=
    (zero_add (z + 0)).trans (add_zero z)
  exact hZero.trans (Category.assoc ((inclusionOfMooreComplexMap Xd).f n)
    (Hd.toChainHomotopy.hom n m) ((DoldKan.PInftyToNormalizedMooreComplex Yd).f m))

/-- The actual native normalized chain-homotopy components are parameter-natural. -/
theorem normalizedFamilyHom_naturality {p q : I} (a : p ⟶ q) (n m : ℕ) :
    ((H.whiskerRight (F.obj p)).toNormalizedChainHomotopy).hom n m ≫
        ((normalizedMooreComplex D).map (Functor.whiskerLeft Y (F.map a))).f m =
      ((normalizedMooreComplex D).map (Functor.whiskerLeft X (F.map a))).f n ≫
        ((H.whiskerRight (F.obj q)).toNormalizedChainHomotopy).hom n m := by
  let Xp := X ⋙ F.obj p
  let Xq := X ⋙ F.obj q
  let Yp := Y ⋙ F.obj p
  let Yq := Y ⋙ F.obj q
  let s := Functor.whiskerLeft X (F.map a)
  let t := Functor.whiskerLeft Y (F.map a)
  let A := alternatingFaceMapComplex D
  let N := normalizedMooreComplex D
  let Hp := H.whiskerRight (F.obj p)
  let Hq := H.whiskerRight (F.obj q)
  have hAlt : Hp.toChainHomotopy.hom n m ≫ (A.map t).f m =
      (A.map s).f n ≫ Hq.toChainHomotopy.hom n m :=
    alternatingFamilyHom_naturality F H a n m
  have hι := congrArg (fun z => z.f n) ((inclusionOfMooreComplex D).naturality s)
  change (N.map s).f n ≫ (inclusionOfMooreComplexMap Xq).f n =
    (inclusionOfMooreComplexMap Xp).f n ≫ (A.map s).f n at hι
  have hπ := congrArg (fun z => z.f m) (DoldKan.PInftyToNormalizedMooreComplex_naturality t)
  change (A.map t).f m ≫ (DoldKan.PInftyToNormalizedMooreComplex Yq).f m =
    (DoldKan.PInftyToNormalizedMooreComplex Yp).f m ≫ (N.map t).f m at hπ
  have hCore : Hp.toChainHomotopy.hom n m ≫
        (DoldKan.PInftyToNormalizedMooreComplex Yp).f m ≫ (N.map t).f m =
      (A.map s).f n ≫ Hq.toChainHomotopy.hom n m ≫
        (DoldKan.PInftyToNormalizedMooreComplex Yq).f m :=
    (congrArg (fun z => Hp.toChainHomotopy.hom n m ≫ z) hπ.symm).trans
      ((Category.assoc (Hp.toChainHomotopy.hom n m) ((A.map t).f m)
        ((DoldKan.PInftyToNormalizedMooreComplex Yq).f m)).symm.trans
          ((congrArg (fun z => z ≫ (DoldKan.PInftyToNormalizedMooreComplex Yq).f m) hAlt).trans
            (Category.assoc ((A.map s).f n) (Hq.toChainHomotopy.hom n m)
              ((DoldKan.PInftyToNormalizedMooreComplex Yq).f m))))
  change Hp.toNormalizedChainHomotopy.hom n m ≫ (N.map t).f m =
    (N.map s).f n ≫ Hq.toNormalizedChainHomotopy.hom n m
  have hHp : Hp.toNormalizedChainHomotopy.hom n m =
      (inclusionOfMooreComplexMap Xp).f n ≫ Hp.toChainHomotopy.hom n m ≫
        (DoldKan.PInftyToNormalizedMooreComplex Yp).f m :=
    toNormalizedChainHomotopy_hom Hp n m
  have hHq : Hq.toNormalizedChainHomotopy.hom n m =
      (inclusionOfMooreComplexMap Xq).f n ≫ Hq.toChainHomotopy.hom n m ≫
        (DoldKan.PInftyToNormalizedMooreComplex Yq).f m :=
    toNormalizedChainHomotopy_hom Hq n m
  have hTarget :
      ((inclusionOfMooreComplexMap Xp).f n ≫ Hp.toChainHomotopy.hom n m ≫
        (DoldKan.PInftyToNormalizedMooreComplex Yp).f m) ≫ (N.map t).f m =
      (N.map s).f n ≫ ((inclusionOfMooreComplexMap Xq).f n ≫
        Hq.toChainHomotopy.hom n m ≫ (DoldKan.PInftyToNormalizedMooreComplex Yq).f m) := by
    let ip := (inclusionOfMooreComplexMap Xp).f n
    let iq := (inclusionOfMooreComplexMap Xq).f n
    let hp := Hp.toChainHomotopy.hom n m
    let hq := Hq.toChainHomotopy.hom n m
    let pp := (DoldKan.PInftyToNormalizedMooreComplex Yp).f m
    let pq := (DoldKan.PInftyToNormalizedMooreComplex Yq).f m
    let ns := (N.map s).f n
    let nt := (N.map t).f m
    let as := (A.map s).f n
    have hLeft : (ip ≫ hp ≫ pp) ≫ nt = ip ≫ hp ≫ pp ≫ nt :=
      (Category.assoc ip (hp ≫ pp) nt).trans (congrArg (fun z => ip ≫ z) (Category.assoc hp pp nt))
    have hMiddle : ip ≫ as ≫ hq ≫ pq = ns ≫ iq ≫ hq ≫ pq :=
      (Category.assoc ip as (hq ≫ pq)).symm.trans
        ((congrArg (fun z => z ≫ hq ≫ pq) hι.symm).trans (Category.assoc ns iq (hq ≫ pq)))
    exact hLeft.trans ((congrArg (fun z => ip ≫ z) hCore).trans hMiddle)
  exact (congrArg (fun z => z ≫ (N.map t).f m) hHp).trans
    (hTarget.trans (congrArg (fun z => (N.map s).f n ≫ z) hHq).symm)

end Normalized

end CategoryTheory.SimplicialObject.Homotopy

end
