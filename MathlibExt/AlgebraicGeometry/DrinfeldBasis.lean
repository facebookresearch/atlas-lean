/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_RelEffCartierDivOfPoint.lean`,
`Definitions/Def_AlgebraicGeometry_RelEffCartierDivSum.lean`,
`Definitions/Def_WeierstrassCurve_ProjModel.lean`,
`Definitions/Def_WeierstrassCurve_DrinfeldBasisGlobal.lean` and the
solution file for the flat torsion-ideal theorem in `P2M/Sol/`

(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEndDegree

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S}

/-- The graph of a morphism over a common base, as a morphism into the
pullback. -/
noncomputable def graphOver (a : T ⟶ 𝒞) (ha : a ≫ f = g) : T ⟶ pullback f g :=
  pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm)

theorem graphOver_eq_lift (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha =
      pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm) :=
  rfl

@[reassoc (attr := simp)]
theorem graphOver_fst (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.fst f g = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphOver_snd (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.snd f g = 𝟙 T :=
  pullback.lift_snd _ _ _

instance isClosedImmersion_graphOver [IsSeparated f] (a : T ⟶ 𝒞)
    (ha : a ≫ f = g) : IsClosedImmersion (graphOver f a ha) := by
  have : IsClosedImmersion (graphOver f a ha ≫ pullback.snd f g) := by
    rw [graphOver_snd]; infer_instance
  exact .of_comp (graphOver f a ha) (pullback.snd f g)

variable {r : ℕ}

/-- The product of the graph kernels of a finite family of morphisms over
a common base. -/
noncomputable def prodKerGraph (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    (pullback f g).IdealSheafData :=
  ∏ i, (graphOver f (a i) (ha i)).ker

theorem prodKerGraph_eq_prod (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f a ha = ∏ i, (graphOver f (a i) (ha i)).ker :=
  rfl

@[simp]
theorem prodKerGraph_zero (a : Fin 0 → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f a ha = ⊤ := by
  simp [prodKerGraph]

@[simp]
theorem prodKerGraph_one (a : Fin 1 → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f a ha = (graphOver f (a 0) (ha 0)).ker := by
  simp [prodKerGraph]

theorem prodKerGraph_succ (a : Fin (r + 1) → (T ⟶ 𝒞))
    (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f a ha = (graphOver f (a 0) (ha 0)).ker *
      prodKerGraph f (fun i => a i.succ) (fun i => ha i.succ) := by
  simp [prodKerGraph, Fin.prod_univ_succ]

theorem prodKerGraph_comp_equiv (σ : Equiv.Perm (Fin r))
    (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    prodKerGraph f (fun i => a (σ i)) (fun i => ha (σ i)) =
      prodKerGraph f a ha :=
  Equiv.prod_comp σ (fun i => (graphOver f (a i) (ha i)).ker)

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

/-- A point is torsion of order dividing `n` for a relative group law. -/
def IsTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : Over.mk t ⟶ Over.mk f) :
    Prop :=
  G.nsmul t n x = G.one t

theorem isTorsionPoint_def (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : Over.mk t ⟶ Over.mk f) :
    G.IsTorsionPoint t n x ↔ G.nsmul t n x = G.one t :=
  Iff.rfl

end RelativeGroupLaw

namespace DrinfeldGlobal

variable {R : Type u} [CommRing R] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

/-- A section of the underlying scheme over the base. -/
abbrev Section {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) :=
  Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk f

/-- An integral linear combination of two sections. -/
noncomputable def linComb (P Q : Section f) (a b : ℕ) : Section f :=
  G.mul _ (G.nsmul _ a P) (G.nsmul _ b Q)

/-- The `q * q` sections obtained from two sections and their multiples. -/
noncomputable def basisTuple (q : ℕ) (P Q : Section f) :
    Fin (q * q) → (Spec (CommRingCat.of R) ⟶ A) :=
  fun i => (DrinfeldGlobal.linComb G P Q (i.val / q) (i.val % q)).left

theorem basisTuple_over (q : ℕ) (P Q : Section f) (i : Fin (q * q)) :
    DrinfeldGlobal.basisTuple G q P Q i ≫ f = 𝟙 (Spec (CommRingCat.of R)) :=
  Over.w (DrinfeldGlobal.linComb G P Q (i.val / q) (i.val % q))

/-- The divisor determined by the `q * q` basis sections. -/
noncomputable def basisDivisor (q : ℕ) (P Q : Section f) :
    (pullback f (𝟙 (Spec (CommRingCat.of R)))).IdealSheafData :=
  prodKerGraph f (DrinfeldGlobal.basisTuple G q P Q) (DrinfeldGlobal.basisTuple_over G q P Q)

/-- The canonical identification morphism into the pullback along the
identity. -/
noncomputable def toPullbackId : A ⟶ pullback f (𝟙 (Spec (CommRingCat.of R))) :=
  pullback.lift (𝟙 A) f (by simp)

/-- The torsion ideal determined by multiplication by `q`. -/
noncomputable def torsionIdeal (q : ℕ) :
    (pullback f (𝟙 (Spec (CommRingCat.of R)))).IdealSheafData :=
  (pullback.fst (G.schemeNsmul q)
    (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ toPullbackId (f := f)).ker

/-- Two sections form a Drinfeld basis at level `q` when their basis
divisor is the torsion ideal. This is the source predicate;
`IsValidDrinfeldBasis` adds a positive level and `q`-torsion sections. -/
def IsDrinfeldBasis (q : ℕ) (P Q : Section f) : Prop :=
  DrinfeldGlobal.basisDivisor G q P Q = DrinfeldGlobal.torsionIdeal G q

theorem isDrinfeldBasis_iff (q : ℕ) (P Q : Section f) :
    DrinfeldGlobal.IsDrinfeldBasis G q P Q ↔
      DrinfeldGlobal.basisDivisor G q P Q = DrinfeldGlobal.torsionIdeal G q :=
  Iff.rfl

/-- A Drinfeld basis at level `q` with the conditions of a Drinfeld level
structure: the level is positive, both sections are `q`-torsion, and they
satisfy the source predicate `IsDrinfeldBasis`. The extra conditions matter at
small levels: at level one the basis tuple is the unit section alone, so
`IsDrinfeldBasis` holds for every pair, while this predicate holds only for the
unit pair. -/
structure IsValidDrinfeldBasis (q : ℕ) (P Q : Section f) : Prop where
  /-- The level is positive. -/
  level_pos : 0 < q
  /-- The first section is `q`-torsion. -/
  isTorsionPoint_fst : G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) q P
  /-- The second section is `q`-torsion. -/
  isTorsionPoint_snd : G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) q Q
  /-- The basis divisor is the torsion ideal. -/
  isDrinfeldBasis : DrinfeldGlobal.IsDrinfeldBasis G q P Q

theorem isValidDrinfeldBasis_iff (q : ℕ) (P Q : Section f) :
    DrinfeldGlobal.IsValidDrinfeldBasis G q P Q ↔
      0 < q ∧ G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) q P ∧
        G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of R))) q Q ∧
        DrinfeldGlobal.IsDrinfeldBasis G q P Q :=
  ⟨fun h => ⟨h.level_pos, h.isTorsionPoint_fst, h.isTorsionPoint_snd, h.isDrinfeldBasis⟩,
    fun ⟨hq, hP, hQ, h⟩ => ⟨hq, hP, hQ, h⟩⟩

/-- The torsion subscheme is flat over the base whenever the scheme
kernel of multiplication by `n` is flat over the base. -/
theorem flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr
    [IsSeparated f] (n : ℕ)
    (h : Flat (pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).left)) :
    Flat ((DrinfeldGlobal.torsionIdeal G n).subschemeι ≫
      pullback.snd f (𝟙 (Spec (CommRingCat.of R)))) := by
  have hone : (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ f =
      𝟙 (Spec (CommRingCat.of R)) :=
    Over.w (G.one (𝟙 (Spec (CommRingCat.of R))))
  haveI : IsClosedImmersion (G.one (𝟙 (Spec (CommRingCat.of R)))).left := by
    have : IsClosedImmersion
        ((G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ f) := by
      rw [hone]
      exact {
        stalkMap_surjective := fun x ↦
          (ConcreteCategory.bijective_of_isIso
            (Scheme.Hom.stalkMap (𝟙 (Spec (CommRingCat.of R))) x)).2
        isClosedEmbedding := Homeomorph.isClosedEmbedding <|
          TopCat.homeoOfIso (asIso
            ((𝟙 (Spec (CommRingCat.of R)) :
              (Spec (CommRingCat.of R)) ⟶ (Spec (CommRingCat.of R))).base)) }
    exact IsClosedImmersion.of_comp _ f
  haveI : IsIso (toPullbackId (f := f)) :=
    ⟨⟨pullback.fst f (𝟙 (Spec (CommRingCat.of R))),
      pullback.lift_fst _ _ _, by
        apply pullback.hom_ext
        · simp only [Category.assoc, toPullbackId, pullback.lift_fst,
            Category.id_comp, Category.comp_id]
        · simp only [Category.assoc, toPullbackId, pullback.lift_snd,
            Category.id_comp, Category.comp_id, pullback.condition]⟩⟩
  have hstr : (pullback.fst (G.schemeNsmul n)
        (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ toPullbackId (f := f)) ≫
        pullback.snd f (𝟙 (Spec (CommRingCat.of R))) =
      pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).left := by
    rw [Category.assoc,
      show toPullbackId (f := f) ≫ pullback.snd f (𝟙 (Spec (CommRingCat.of R))) = f from
        pullback.lift_snd _ _ _]
    calc pullback.fst (G.schemeNsmul n)
          (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ f
        = pullback.fst (G.schemeNsmul n)
            (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫
            (G.schemeNsmul n ≫ f) := by rw [G.schemeNsmul_comp n]
      _ = pullback.snd (G.schemeNsmul n)
            (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫
            (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ f := by
          rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = pullback.snd (G.schemeNsmul n)
            (G.one (𝟙 (Spec (CommRingCat.of R)))).left := by
          rw [hone]
          exact Category.comp_id _
  change Flat ((Scheme.Hom.imageι (pullback.fst (G.schemeNsmul n)
      (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ toPullbackId (f := f))) ≫
      pullback.snd f (𝟙 (Spec (CommRingCat.of R))))
  haveI : MorphismProperty.RespectsIso @Flat := by
    rw [HasRingHomProperty.eq_affineLocally @Flat]
    exact affineLocally_respectsIso (P := RingHom.Flat) RingHom.Flat.respectsIso
  refine ((MorphismProperty.cancel_left_of_respectsIso @Flat)
    (Scheme.Hom.toImage (pullback.fst (G.schemeNsmul n)
      (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ toPullbackId (f := f)))
    ((Scheme.Hom.imageι (pullback.fst (G.schemeNsmul n)
      (G.one (𝟙 (Spec (CommRingCat.of R)))).left ≫ toPullbackId (f := f))) ≫
      pullback.snd f (𝟙 (Spec (CommRingCat.of R))))).mp ?_
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  exact hstr ▸ h

end DrinfeldGlobal

end AlgebraicGeometry
