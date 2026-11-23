/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Groupoid.BasedFunctor
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellCollarDeformation
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.CategoryTheory.Conj

/-!
# The quotient-valued functor on the actual outer collar

Compose the original outer-region retraction with the normalized based
groupoid functor for the original normal-subgroup quotient. Its restriction
along the original inclusion is strictly the same normalized source functor.
At the included original basepoint its End homomorphism is the quotient of
the original equality-pointed retraction map, with both actual endpoint casts.

These constructions retain the original attachment and all positive cell
dimensions and index families, including an empty family. The local results
require neither connectedness nor perfectness and do not construct a functor
on the entire attachment or a quotient isomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellQuotientFunctor

variable {ι : Type u}

/-- The actual outer retraction recovers the original included basepoint. -/
theorem retraction_includedBasepoint (X : TopCat.{u}) (x : X) (n : ℕ)
    (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    CellCollarDeformation.retractionU X n a
      (CellCollarDeformation.inclusionU X n a x) = x := by
  let j := CellCollarDeformation.inclusionU X n a
  let r := CellCollarDeformation.retractionU X n a
  have h : (j ≫ r) x = x :=
    ConcreteCategory.congr_hom
      (CellCollarDeformation.inclusionU_retractionU X n a) x
  exact (TopCat.comp_app j r x).symm.trans h

variable (X : TopCat.{u}) (x : X)
variable (P : Subgroup (FundamentalGroup X x)) [P.Normal]
variable (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The original normal-subgroup quotient functor on the actual outer region. -/
def kappaU :
    FundamentalGroupoid (CellCollarCover.U X n a) ⥤
      SingleObj (FundamentalGroup X x ⧸ P) :=
  FundamentalGroupoid.map (CellCollarDeformation.retractionU X n a).hom ⋙
    Groupoid.basedFunctor (FundamentalGroupoid.mk x) (QuotientGroup.mk' P)

/-- Along the original inclusion, the constructed functor strictly recovers
the normalized based functor of the same original quotient homomorphism. -/
theorem kappaU_originalInclusion :
    FundamentalGroupoid.map (CellCollarDeformation.inclusionU X n a).hom ⋙
      kappaU X x P n a =
        Groupoid.basedFunctor (FundamentalGroupoid.mk x) (QuotientGroup.mk' P) := by
  let j := CellCollarDeformation.inclusionU X n a
  let r := CellCollarDeformation.retractionU X n a
  let B : FundamentalGroupoid X ⥤ SingleObj (FundamentalGroup X x ⧸ P) :=
    Groupoid.basedFunctor (FundamentalGroupoid.mk x) (QuotientGroup.mk' P)
  have hC : r.hom.comp j.hom = ContinuousMap.id X := by
    simpa only [TopCat.hom_comp, TopCat.hom_id] using
      congrArg (fun f : X ⟶ X => f.hom)
        (CellCollarDeformation.inclusionU_retractionU X n a)
  have hJR :
      FundamentalGroupoid.map j.hom ⋙ FundamentalGroupoid.map r.hom =
        𝟭 (FundamentalGroupoid X) :=
    (FundamentalGroupoid.map_comp r.hom j.hom).symm.trans
      ((congrArg (fun f : C(X, X) => FundamentalGroupoid.map f) hC).trans
        (FundamentalGroupoid.map_id (X := X)))
  calc
    _ = (FundamentalGroupoid.map j.hom ⋙ FundamentalGroupoid.map r.hom) ⋙ B := rfl
    _ = (𝟭 (FundamentalGroupoid X)) ⋙ B :=
      congrArg (fun F : FundamentalGroupoid X ⥤ FundamentalGroupoid X => F ⋙ B) hJR
    _ = B := Functor.id_comp B

/-- The complete original End homomorphism is the quotient map after the
actual equality-pointed outer retraction map. -/
theorem kappaU_originalEnd :
    (SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm.toMonoidHom.comp
      ((kappaU X x P n a).mapEnd
        (FundamentalGroupoid.mk (CellCollarDeformation.inclusionU X n a x))) =
      (QuotientGroup.mk' P).comp
        (FundamentalGroup.mapOfEq (CellCollarDeformation.retractionU X n a).hom
          (retraction_includedBasepoint X x n a)) := by
  let j := CellCollarDeformation.inclusionU X n a
  let r := CellCollarDeformation.retractionU X n a
  let B : FundamentalGroupoid X ⥤ SingleObj (FundamentalGroup X x ⧸ P) :=
    Groupoid.basedFunctor (FundamentalGroupoid.mk x) (QuotientGroup.mk' P)
  let R : FundamentalGroupoid (CellCollarCover.U X n a) ⥤ FundamentalGroupoid X :=
    FundamentalGroupoid.map r.hom
  let cU : FundamentalGroupoid (CellCollarCover.U X n a) :=
    FundamentalGroupoid.mk (j x)
  have hr : r.hom (j x) = x := retraction_includedBasepoint X x n a
  let α : R.obj cU ≅ FundamentalGroupoid.mk x :=
    eqToIso (congrArg FundamentalGroupoid.mk hr)
  have hα : B.mapIso α = Iso.refl (SingleObj.star (FundamentalGroup X x ⧸ P)) := by
    change B.mapIso (eqToIso (congrArg FundamentalGroupoid.mk hr)) =
      Iso.refl (SingleObj.star (FundamentalGroup X x ⧸ P))
    rw [eqToIso_map]
    exact eqToIso_refl _
  apply MonoidHom.ext
  intro q
  have hconj :
      B.map (α.conj (R.mapEnd cU q)).asHom = B.map (R.map q.asHom) := by
    calc
      _ = ((B.mapIso α).conj (B.mapEnd (R.obj cU) (R.mapEnd cU q))).asHom :=
        B.map_conj α (R.mapEnd cU q)
      _ = ((Iso.refl (SingleObj.star (FundamentalGroup X x ⧸ P))).conj
          (B.mapEnd (R.obj cU) (R.mapEnd cU q))).asHom := by rw [hα]
      _ = (B.mapEnd (R.obj cU) (R.mapEnd cU q)).asHom := by rw [Iso.refl_conj]
      _ = _ := rfl
  have hbase :
      B.map (α.conj (R.mapEnd cU q)).asHom =
        QuotientGroup.mk' P (α.conj (R.mapEnd cU q)) :=
    Groupoid.basedFunctor_map_end (FundamentalGroupoid.mk x)
      (QuotientGroup.mk' P) (α.conj (R.mapEnd cU q))
  change B.map (R.map q.asHom) =
    QuotientGroup.mk' P (α.conj (R.mapEnd cU q))
  exact hconj.symm.trans hbase

/-- The same original End formula explicitly retains both reversed
basepoint-equality casts on the actual mapped path class. -/
theorem kappaU_originalEnd_cast
    (q : FundamentalGroup (CellCollarCover.U X n a)
      (CellCollarDeformation.inclusionU X n a x)) :
    (kappaU X x P n a).map q.asHom =
      QuotientGroup.mk' P
        (FundamentalGroup.fromPath
          ((Path.Homotopic.Quotient.map q.asHom
            (CellCollarDeformation.retractionU X n a).hom).cast
              (retraction_includedBasepoint X x n a).symm
              (retraction_includedBasepoint X x n a).symm)) := by
  have h := congrArg
    (fun φ : FundamentalGroup (CellCollarCover.U X n a)
        (CellCollarDeformation.inclusionU X n a x) →* (FundamentalGroup X x ⧸ P) => φ q)
    (kappaU_originalEnd X x P n a)
  change (kappaU X x P n a).map q.asHom =
    QuotientGroup.mk' P
      (FundamentalGroup.mapOfEq (CellCollarDeformation.retractionU X n a).hom
        (retraction_includedBasepoint X x n a) q) at h
  exact h.trans (congrArg (QuotientGroup.mk' P)
    (FundamentalGroup.mapOfEq_apply (CellCollarDeformation.retractionU X n a).hom
      (retraction_includedBasepoint X x n a) q))

/-- The original equality-pointed inclusion followed by the constructed
outer End map recovers the same original quotient homomorphism. -/
theorem kappaU_originalInclusionEnd :
    ((SingleObj.toEnd (FundamentalGroup X x ⧸ P)).symm.toMonoidHom.comp
      ((kappaU X x P n a).mapEnd
        (FundamentalGroupoid.mk (CellCollarDeformation.inclusionU X n a x)))).comp
      (FundamentalGroup.mapOfEq (CellCollarDeformation.inclusionU X n a).hom
        (rfl : CellCollarDeformation.inclusionU X n a x =
          CellCollarDeformation.inclusionU X n a x)) = QuotientGroup.mk' P := by
  rw [FundamentalGroup.mapOfEq_rfl]
  apply MonoidHom.ext
  intro q
  have hF := kappaU_originalInclusion X x P n a
  have hq :
      (FundamentalGroupoid.map (CellCollarDeformation.inclusionU X n a).hom ⋙
        kappaU X x P n a).map q.asHom =
          (Groupoid.basedFunctor (FundamentalGroupoid.mk x) (QuotientGroup.mk' P)).map
            q.asHom :=
    congrArg
      (fun F : FundamentalGroupoid X ⥤ SingleObj (FundamentalGroup X x ⧸ P) =>
        (F.map q.asHom : FundamentalGroup X x ⧸ P)) hF
  change (kappaU X x P n a).map
      ((FundamentalGroupoid.map (CellCollarDeformation.inclusionU X n a).hom).map q.asHom) =
        QuotientGroup.mk' P q
  exact hq.trans
    (Groupoid.basedFunctor_map_end (FundamentalGroupoid.mk x) (QuotientGroup.mk' P) q)

end AlgebraicTopology.CellQuotientFunctor

end

end
