/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.Unitization.Map
public import MathlibExt.Algebra.Algebra.Unitization.Unital
public import MathlibExt.KTheory.Ring.Comparison.ScalarExtensionK0Coherence
public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionFunctorCoherence
public import MathlibExt.KTheory.Ring.K0.Product
public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel.NonunitalMap
public import MathlibExt.KTheory.Exact.K0.Equivalence

/-!
# Nonunital algebraic K₀

The group is the actual augmentation kernel of projective-module K₀ of the
integer unitization. Its coefficient maps use the original associative-ring
scalar extension, retaining independent ring universes.

The unital ring chart is `(n,r) ↦ (n,n·1+r)` from Weibel II.Exercise 2.4.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v w

namespace AlgebraicKTheory

namespace RingK0

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- Projective induction along a nonunital map between unital rings, using the
actual finite-idempotent model and its original projective realization. -/
def mapNonUnitalRingHom (f : R →ₙ+* S) : RingK0 R →+ RingK0 S :=
  (K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence S)).toAddMonoidHom.comp
    ((K0.map (FGProjectiveCat.IdempotentModel.NonunitalMap.functor f)).comp
      (K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence R)).symm.toAddMonoidHom)

/-- The map on every original finite-idempotent projective class. -/
theorem mapNonUnitalRingHom_model_mk (f : R →ₙ+* S)
    (P : FGProjectiveCat.IdempotentModel R) :
    mapNonUnitalRingHom f
        (K0.mk ((FGProjectiveCat.IdempotentModel.equivalence R).functor.obj P)) =
      K0.mk ((FGProjectiveCat.IdempotentModel.equivalence S).functor.obj
        (FGProjectiveCat.IdempotentModel.NonunitalMap.obj f P)) := by
  change (K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence S))
      (K0.map (FGProjectiveCat.IdempotentModel.NonunitalMap.functor f)
        ((K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence R)).symm
          (K0.mk ((FGProjectiveCat.IdempotentModel.equivalence R).functor.obj P)))) = _
  rw [← K0.equivOfEquivalence_mk (FGProjectiveCat.IdempotentModel.equivalence R) P,
    AddEquiv.symm_apply_apply, K0.map_mk]
  exact K0.equivOfEquivalence_mk (FGProjectiveCat.IdempotentModel.equivalence S)
    (FGProjectiveCat.IdempotentModel.NonunitalMap.obj f P)

private theorem hom_ext_model {G : Type*} [AddCommGroup G] {f g : RingK0 R →+ G}
    (h : ∀ P : FGProjectiveCat.IdempotentModel R,
      f (K0.mk ((FGProjectiveCat.IdempotentModel.equivalence R).functor.obj P)) =
        g (K0.mk ((FGProjectiveCat.IdempotentModel.equivalence R).functor.obj P))) : f = g := by
  let e := K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence R)
  have hc : f.comp e.toAddMonoidHom = g.comp e.toAddMonoidHom := by
    apply K0.hom_ext
    intro P
    change f ((K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence R))
        (K0.mk P)) =
      g ((K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence R)) (K0.mk P))
    rw [K0.equivOfEquivalence_mk]
    exact h P
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun hc y

@[simp]
theorem mapNonUnitalRingHom_id (R : Type u) [Ring R] :
    mapNonUnitalRingHom (NonUnitalRingHom.id R) = AddMonoidHom.id (RingK0 R) := by
  apply hom_ext_model
  intro P
  rw [mapNonUnitalRingHom_model_mk, FGProjectiveCat.IdempotentModel.NonunitalMap.obj_id]
  rfl

/-- Nonunital induction composes on the actual original projective K₀ groups. -/
theorem mapNonUnitalRingHom_comp (f : R →ₙ+* S) (g : S →ₙ+* T) :
    mapNonUnitalRingHom (g.comp f) = (mapNonUnitalRingHom g).comp (mapNonUnitalRingHom f) := by
  apply hom_ext_model
  intro P
  simp only [AddMonoidHom.comp_apply, mapNonUnitalRingHom_model_mk]
  rw [FGProjectiveCat.IdempotentModel.NonunitalMap.obj_comp]

/-- The zero coefficient map sends every actual finite projective class to zero. -/
@[simp]
theorem mapNonUnitalRingHom_zero :
    mapNonUnitalRingHom (0 : R →ₙ+* S) = 0 := by
  apply hom_ext_model
  intro P
  rw [mapNonUnitalRingHom_model_mk]
  have h := congrArg (K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence S))
    (K0.mk_eq_zero_of_isZero
      (FGProjectiveCat.IdempotentModel.NonunitalMap.obj_zero_isZero (S := S) P))
  simpa only [K0.equivOfEquivalence_mk, map_zero, AddMonoidHom.zero_apply] using h

/-- On unital maps this is the same original associative-ring scalar-extension map. -/
theorem mapNonUnitalRingHom_toNonUnitalRingHom (f : R →+* S) :
    mapNonUnitalRingHom f.toNonUnitalRingHom = FGProjectiveCat.scalarExtensionK0 f := by
  apply hom_ext_model
  intro P
  rw [mapNonUnitalRingHom_model_mk, FGProjectiveCat.scalarExtensionK0_mk,
    FGProjectiveCat.IdempotentModel.NonunitalMap.obj_toNonUnitalRingHom]
  exact K0.mk_congr_of_iso (FGProjectiveCat.IdempotentModel.scalarExtensionIso f P).symm

/-- Original scalar extension after nonunital projective induction is the
actual composite coefficient map on every K₀ value. -/
theorem scalarExtensionK0_mapNonUnitalRingHom (f : R →ₙ+* S) (g : S →+* T)
    (x : RingK0 R) :
    FGProjectiveCat.scalarExtensionK0 g (mapNonUnitalRingHom f x) =
      mapNonUnitalRingHom (g.toNonUnitalRingHom.comp f) x := by
  rw [← mapNonUnitalRingHom_toNonUnitalRingHom g, ← AddMonoidHom.comp_apply,
    ← mapNonUnitalRingHom_comp]

open CategoryTheory CategoryTheory.Limits
open FGProjectiveCat FGProjectiveCat.IdempotentModel
open FGProjectiveCat.IdempotentModel.NonunitalMap

private theorem orthogonal_model_class (f g h : R →ₙ+* S)
    (hh : ∀ r, h r = f r + g r)
    (hfg : ∀ r s, f r * g s = 0) (hgf : ∀ r s, g r * f s = 0)
    (P : IdempotentModel R) :
    (K0.mk (obj h P) : K0 (IdempotentModel S)) = K0.mk (obj f P) + K0.mk (obj g P) := by
  let E : IdempotentModel S := obj f P
  let G : IdempotentModel S := obj g P
  let H : IdempotentModel S := obj h P
  let a : Matrix (Fin P.X) (Fin P.X) S := rowHomEquiv S P.X P.X E.p
  let b : Matrix (Fin P.X) (Fin P.X) S := rowHomEquiv S P.X P.X G.p
  let d : Matrix (Fin P.X) (Fin P.X) S := rowHomEquiv S P.X P.X H.p
  have ha : a * a = a := (equivalence_characteristic S).2.2.2.1 E
  have hb : b * b = b := (equivalence_characteristic S).2.2.2.1 G
  have hd : d = a + b := by
    change rowHomEquiv S P.X P.X (obj h P).p =
      rowHomEquiv S P.X P.X (obj f P).p + rowHomEquiv S P.X P.X (obj g P).p
    rw [obj_matrix, obj_matrix, obj_matrix]
    ext i j
    exact hh _
  have hab : a * b = 0 := by
    change rowHomEquiv S P.X P.X (obj f P).p *
      rowHomEquiv S P.X P.X (obj g P).p = 0
    rw [obj_matrix, obj_matrix]
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    exact hfg _ _
  have hba : b * a = 0 := by
    change rowHomEquiv S P.X P.X (obj g P).p *
      rowHomEquiv S P.X P.X (obj f P).p = 0
    rw [obj_matrix, obj_matrix]
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    exact hgf _ _
  have hiCorner : a * a * d = a := by
    rw [ha, hd, mul_add, ha, hab, add_zero]
  have hrCorner : d * a * a = a := by
    rw [hd, add_mul, ha, hba, add_zero, ha]
  have hqCorner : d * b * b = b := by
    rw [hd, add_mul, hab, hb, zero_add, hb]
  have hsCorner : b * b * d = b := by
    rw [hb, hd, mul_add, hba, hb, zero_add]
  let i : E ⟶ H := homOfMatrix S a hiCorner
  let r : H ⟶ E := homOfMatrix S a hrCorner
  let q : H ⟶ G := homOfMatrix S b hqCorner
  let s : G ⟶ H := homOfMatrix S b hsCorner
  have hi : rowHomEquiv S P.X P.X i.f = a :=
    homOfMatrix_matrix S (P := E) (Q := H) a hiCorner
  have hr : rowHomEquiv S P.X P.X r.f = a :=
    homOfMatrix_matrix S (P := H) (Q := E) a hrCorner
  have hq : rowHomEquiv S P.X P.X q.f = b :=
    homOfMatrix_matrix S (P := H) (Q := G) b hqCorner
  have hs : rowHomEquiv S P.X P.X s.f = b :=
    homOfMatrix_matrix S (P := G) (Q := H) b hsCorner
  have cmp {U V W : IdempotentModel S} (p : U ⟶ V) (q : V ⟶ W) :
      rowHomEquiv S U.X W.X (p ≫ q).f =
        rowHomEquiv S U.X V.X p.f * rowHomEquiv S V.X W.X q.f :=
    (equivalence_characteristic S).2.2.1 U.X V.X W.X p.f q.f
  have hir : i ≫ r = 𝟙 E := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv S P.X P.X).injective
    change rowHomEquiv S P.X P.X (i ≫ r).f = a
    rw [cmp i r]
    change rowHomEquiv S P.X P.X i.f * rowHomEquiv S P.X P.X r.f = a
    rw [hi, hr, ha]
  have hsq : s ≫ q = 𝟙 G := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv S P.X P.X).injective
    change rowHomEquiv S P.X P.X (s ≫ q).f = b
    rw [cmp s q]
    change rowHomEquiv S P.X P.X s.f * rowHomEquiv S P.X P.X q.f = b
    rw [hs, hq, hb]
  have hiq : i ≫ q = 0 := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv S P.X P.X).injective
    change rowHomEquiv S P.X P.X (i ≫ q).f = rowHomEquiv S P.X P.X 0
    rw [cmp i q, map_zero]
    change rowHomEquiv S P.X P.X i.f * rowHomEquiv S P.X P.X q.f = 0
    rw [hi, hq, hab]
  have hTotal : r ≫ i + q ≫ s = 𝟙 H := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv S P.X P.X).injective
    change rowHomEquiv S P.X P.X ((r ≫ i).f + (q ≫ s).f) = d
    rw [(rowHomEquiv S P.X P.X).map_add, cmp r i, cmp q s]
    change rowHomEquiv S P.X P.X r.f * rowHomEquiv S P.X P.X i.f +
      rowHomEquiv S P.X P.X q.f * rowHomEquiv S P.X P.X s.f = d
    rw [hr, hi, hq, hs, ha, hb, hd]
  let C : ShortComplex (IdempotentModel S) := ShortComplex.mk i q hiq
  let split : C.Splitting := { r := r, s := s, f_r := hir, s_g := hsq, id := hTotal }
  exact K0.mk_eq_of_admissibleExact (ExactCategory.isAdmissibleExact_of_splitting split)


/-- Orthogonal coefficient maps induce the sum of their actual projective K₀ maps. -/
theorem mapNonUnitalRingHom_add_of_orthogonal (f g h : R →ₙ+* S)
    (hh : ∀ r, h r = f r + g r)
    (hfg : ∀ r s, f r * g s = 0) (hgf : ∀ r s, g r * f s = 0) :
    mapNonUnitalRingHom h = mapNonUnitalRingHom f + mapNonUnitalRingHom g := by
  apply hom_ext_model
  intro P
  simp only [AddMonoidHom.add_apply, mapNonUnitalRingHom_model_mk]
  have hc := congrArg (K0.equivOfEquivalence (FGProjectiveCat.IdempotentModel.equivalence S))
    (orthogonal_model_class f g h hh hfg hgf P)
  simpa only [K0.equivOfEquivalence_mk, map_add] using hc

end RingK0

-- Use the weak structures of the existing unitization Ring throughout the K₀ maps.
local instance integerUnitizationSemiring (I : Type u) [NonUnitalRing I] :
    Semiring (Unitization ℤ I) :=
  (inferInstance : Ring (Unitization ℤ I)).toSemiring

local instance integerUnitizationNonAssocSemiring (I : Type u) [NonUnitalRing I] :
    NonAssocSemiring (Unitization ℤ I) :=
  (inferInstance : Ring (Unitization ℤ I)).toSemiring.toNonAssocSemiring

local instance integerUnitizationNonUnitalNonAssocSemiring (I : Type u) [NonUnitalRing I] :
    NonUnitalNonAssocSemiring (Unitization ℤ I) :=
  (inferInstance : Ring (Unitization ℤ I)).toNonUnitalNonAssocSemiring

namespace NonunitalK0

/-- The actual integer augmentation of a nonunital ring. -/
abbrev augmentation (I : Type u) [NonUnitalRing I] : Unitization ℤ I →+* ℤ :=
  (Unitization.fstHom ℤ I).toRingHom

@[simp]
theorem augmentation_apply {I : Type u} [NonUnitalRing I] (x : Unitization ℤ I) :
    augmentation I x = x.fst :=
  rfl

/-- Unitization of the same nonunital coefficient map, leaving the integer intact. -/
abbrev unitizationMap {I : Type u} {J : Type v} [NonUnitalRing I] [NonUnitalRing J]
    (f : I →ₙ+* J) : Unitization ℤ I →+* Unitization ℤ J :=
  let fZ : I →ₙₐ[ℤ] J := { f with toFun := f, map_smul' n x := map_zsmul f n x }
  (Unitization.mapAlgHom ℤ I fZ).toRingHom

/-- The canonical algebra lift has the same original coefficient pair in
the ring-homomorphism world used by projective K₀. -/
theorem unitizationMap_apply {I : Type u} {J : Type v}
    [NonUnitalRing I] [NonUnitalRing J] (f : I →ₙ+* J) (x : Unitization ℤ I) :
    unitizationMap f x = Unitization.mk (x.fst, f x.snd) := by
  let fZ : I →ₙₐ[ℤ] J := { f with toFun := f, map_smul' n y := map_zsmul f n y }
  let g := Unitization.mapAlgHom ℤ I fZ
  have hcast : g.toRingHom x = g x := congrFun (AlgHom.coe_toRingHom g) x
  exact hcast.trans (Unitization.mapAlgHom_apply ℤ I fZ x)

@[simp]
theorem unitizationMap_fst {I : Type u} {J : Type v}
    [NonUnitalRing I] [NonUnitalRing J] (f : I →ₙ+* J) (x : Unitization ℤ I) :
    (unitizationMap f x).fst = x.fst :=
  congrArg (fun y : Unitization ℤ J => y.fst) (unitizationMap_apply f x)

@[simp]
theorem unitizationMap_snd {I : Type u} {J : Type v}
    [NonUnitalRing I] [NonUnitalRing J] (f : I →ₙ+* J) (x : Unitization ℤ I) :
    (unitizationMap f x).snd = f x.snd :=
  congrArg (fun y : Unitization ℤ J => y.snd) (unitizationMap_apply f x)

/-- The actual unitized map retains injectivity of the nonunital coefficient map. -/
theorem unitizationMap_injective {I : Type u} {J : Type v}
    [NonUnitalRing I] [NonUnitalRing J] (f : I →ₙ+* J) (hf : Function.Injective f) :
    Function.Injective (unitizationMap f) := by
  intro x y h
  apply Unitization.ext
  · simpa only [unitizationMap_fst] using congrArg (fun z : Unitization ℤ J => z.fst) h
  · apply hf
    simpa only [unitizationMap_snd] using congrArg (fun z : Unitization ℤ J => z.snd) h

/-- The actual nonunital inclusion into the integer unitization. -/
abbrev inclusion (I : Type u) [NonUnitalRing I] : I →ₙ+* Unitization ℤ I :=
  (Unitization.inrNonUnitalAlgHom ℤ I : I →ₙ+* Unitization ℤ I)

@[simp]
theorem inclusion_apply {I : Type u} [NonUnitalRing I] (x : I) :
    inclusion I x = Unitization.mk (0, x) :=
  rfl

/-- Both original coefficient maps commute with the same unitization inclusions. -/
theorem unitizationMap_inclusion {I : Type u} {J : Type v}
    [NonUnitalRing I] [NonUnitalRing J] (f : I →ₙ+* J) :
    (unitizationMap f).toNonUnitalRingHom.comp (inclusion I) = (inclusion J).comp f := by
  apply NonUnitalRingHom.ext
  intro x
  apply Unitization.ext
  · change (unitizationMap f (inclusion I x)).fst = (inclusion J (f x)).fst
    rw [unitizationMap_fst, inclusion_apply, inclusion_apply]
  · change (unitizationMap f (inclusion I x)).snd = (inclusion J (f x)).snd
    rw [unitizationMap_snd, inclusion_apply, inclusion_apply]

/-- The same integer augmentation commutes with the actual lifted map. -/
theorem augmentation_unitizationMap {I : Type u} {J : Type v}
    [NonUnitalRing I] [NonUnitalRing J] (f : I →ₙ+* J) :
    (augmentation J).comp (unitizationMap f) = augmentation I := by
  ext x
  change augmentation J (unitizationMap f x) = augmentation I x
  rw [augmentation_apply, unitizationMap_fst, augmentation_apply]

@[simp]
theorem unitizationMap_id (I : Type u) [NonUnitalRing I] :
    unitizationMap (NonUnitalRingHom.id I) = RingHom.id (Unitization ℤ I) := by
  apply RingHom.ext
  intro x
  apply Unitization.ext
  · change (unitizationMap (NonUnitalRingHom.id I) x).fst = x.fst
    exact unitizationMap_fst _ x
  · change (unitizationMap (NonUnitalRingHom.id I) x).snd = x.snd
    exact unitizationMap_snd _ x

/-- Both original nonunital maps compose on their original coefficient. -/
theorem unitizationMap_comp {I : Type u} {J : Type v} {K : Type w}
    [NonUnitalRing I] [NonUnitalRing J] [NonUnitalRing K]
    (f : I →ₙ+* J) (g : J →ₙ+* K) :
    unitizationMap (g.comp f) = (unitizationMap g).comp (unitizationMap f) := by
  apply RingHom.ext
  intro x
  apply Unitization.ext
  · change (unitizationMap (g.comp f) x).fst = (unitizationMap g (unitizationMap f x)).fst
    rw [unitizationMap_fst, unitizationMap_fst, unitizationMap_fst]
  · change (unitizationMap (g.comp f) x).snd = (unitizationMap g (unitizationMap f x)).snd
    rw [unitizationMap_snd, unitizationMap_snd, unitizationMap_snd]
    rfl


end NonunitalK0

/-- Nonunital algebraic K₀ is the actual reduced K₀ of the integer unitization. -/
abbrev NonunitalK0 (I : Type u) [NonUnitalRing I] : Type (u + 1) :=
  ↥(FGProjectiveCat.scalarExtensionK0 (NonunitalK0.augmentation I)).ker

namespace NonunitalK0

/-- The actual augmentation-kernel map induced by a nonunital ring homomorphism. -/
def map {I : Type u} {J : Type v} [NonUnitalRing I] [NonUnitalRing J]
    (f : I →ₙ+* J) : NonunitalK0 I →+ NonunitalK0 J where
  toFun x := ⟨FGProjectiveCat.scalarExtensionK0 (unitizationMap f) x.val, by
    change FGProjectiveCat.scalarExtensionK0 (augmentation J)
      (FGProjectiveCat.scalarExtensionK0 (unitizationMap f) x.val) = 0
    calc
      _ = FGProjectiveCat.scalarExtensionK0
          ((augmentation J).comp (unitizationMap f)) x.val :=
        (DFunLike.congr_fun (FGProjectiveCat.scalarExtensionK0_comp (unitizationMap f) (augmentation J))
          x.val).symm
      _ = FGProjectiveCat.scalarExtensionK0 (augmentation I) x.val := by
        rw [augmentation_unitizationMap]
      _ = 0 := x.property⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ x.val y.val

/-- The native map retains the same original scalar-extension K₀ value. -/
@[simp]
theorem map_val {I : Type u} {J : Type v} [NonUnitalRing I] [NonUnitalRing J]
    (f : I →ₙ+* J) (x : NonunitalK0 I) :
    (map f x).val = FGProjectiveCat.scalarExtensionK0 (unitizationMap f) x.val :=
  rfl

@[simp]
theorem map_id (I : Type u) [NonUnitalRing I] :
    map (NonUnitalRingHom.id I) = AddMonoidHom.id (NonunitalK0 I) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change FGProjectiveCat.scalarExtensionK0 (unitizationMap (NonUnitalRingHom.id I)) x.val =
    x.val
  rw [unitizationMap_id, FGProjectiveCat.scalarExtensionK0_id]
  rfl

/-- The original reduced maps compose through the actual unitized ring maps. -/
theorem map_comp {I : Type u} {J : Type v} {K : Type w}
    [NonUnitalRing I] [NonUnitalRing J] [NonUnitalRing K]
    (f : I →ₙ+* J) (g : J →ₙ+* K) :
    map (g.comp f) = (map g).comp (map f) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change FGProjectiveCat.scalarExtensionK0 (unitizationMap (g.comp f)) x.val =
    FGProjectiveCat.scalarExtensionK0 (unitizationMap g)
      (FGProjectiveCat.scalarExtensionK0 (unitizationMap f) x.val)
  rw [unitizationMap_comp, FGProjectiveCat.scalarExtensionK0_comp]
  rfl

/-- Evaluation of the integer unitization of an already unital ring. -/
abbrev evaluation (R : Type u) [Ring R] : Unitization ℤ R →+* R :=
  (Unitization.lift (NonUnitalAlgHom.id ℤ R)).toRingHom

@[simp]
theorem evaluation_apply {R : Type u} [Ring R] (x : Unitization ℤ R) :
    evaluation R x = (x.fst : R) + x.snd :=
  rfl

/-- The exact unital compatibility ring chart, keeping the original integer and coefficient. -/
abbrev unitizationUnitalEquiv (R : Type u) [Ring R] : Unitization ℤ R ≃+* ℤ × R :=
  (Unitization.unitalProdAlgEquiv ℤ R).toRingEquiv

@[simp]
theorem unitizationUnitalEquiv_apply {R : Type u} [Ring R] (x : Unitization ℤ R) :
    unitizationUnitalEquiv R x = (x.fst, (x.fst : R) + x.snd) := by
  simpa only [unitizationUnitalEquiv, AlgEquiv.coe_toRingEquiv, Int.smul_one_eq_cast]
    using Unitization.unitalProdAlgEquiv_apply ℤ R x

@[simp]
theorem unitizationUnitalEquiv_symm_apply {R : Type u} [Ring R] (x : ℤ × R) :
    (unitizationUnitalEquiv R).symm x = Unitization.mk (x.1, x.2 - (x.1 : R)) := by
  change (Unitization.unitalProdAlgEquiv ℤ R).symm x = _
  rw [Unitization.unitalProdAlgEquiv_symm_apply]
  apply Unitization.ext
  · simp only [Unitization.fst_add, Unitization.fst_inl, Unitization.fst_inr, add_zero]
  · simp only [Unitization.snd_add, Unitization.snd_inl, Unitization.snd_inr,
      zero_add, Int.smul_one_eq_cast]

/-- The original integer complement, obtained from the first product inclusion. -/
def unitalIntegerComplement (R : Type u) [Ring R] : ℤ →ₙ+* Unitization ℤ R where
  toFun n := (NonunitalK0.unitizationUnitalEquiv R).symm (n, 0)
  map_zero' := (NonunitalK0.unitizationUnitalEquiv R).symm.map_zero
  map_add' n m := by
    simpa using (NonunitalK0.unitizationUnitalEquiv R).symm.map_add (n, 0) (m, 0)
  map_mul' n m := by
    simpa using (NonunitalK0.unitizationUnitalEquiv R).symm.map_mul (n, 0) (m, 0)

/-- The original nonunital inclusion of R into its integer unitization. -/
def unitalRingInclusion (R : Type u) [Ring R] : R →ₙ+* Unitization ℤ R where
  toFun r := (NonunitalK0.unitizationUnitalEquiv R).symm (0, r)
  map_zero' := (NonunitalK0.unitizationUnitalEquiv R).symm.map_zero
  map_add' r s := by
    simp
  map_mul' r s := by
    simp

theorem unitalIntegerComplement_apply (R : Type u) [Ring R] (n : ℤ) :
    unitalIntegerComplement R n = Unitization.mk (n, -(n : R)) := by
  change (NonunitalK0.unitizationUnitalEquiv R).symm (n, 0) = _
  rw [NonunitalK0.unitizationUnitalEquiv_symm_apply]
  simp

theorem unitalRingInclusion_apply (R : Type u) [Ring R] (r : R) :
    unitalRingInclusion R r = Unitization.mk (0, r) := by
  change (NonunitalK0.unitizationUnitalEquiv R).symm (0, r) = _
  rw [NonunitalK0.unitizationUnitalEquiv_symm_apply]
  simp

/-- The inverse product chart uses the literal original nonunital inclusion. -/
theorem unitalRingInclusion_eq_inclusion (R : Type u) [Ring R] :
    unitalRingInclusion R = inclusion R := by
  apply NonUnitalRingHom.ext
  intro r
  rw [unitalRingInclusion_apply, inclusion_apply]

private def unitalIntegerProjector (R : Type u) [Ring R] : Unitization ℤ R →ₙ+* Unitization ℤ R :=
  (unitalIntegerComplement R).comp (NonunitalK0.augmentation R).toNonUnitalRingHom

private def unitalRingProjector (R : Type u) [Ring R] : Unitization ℤ R →ₙ+* Unitization ℤ R :=
  (unitalRingInclusion R).comp (NonunitalK0.evaluation R).toNonUnitalRingHom

private theorem unitalSplit_apply (R : Type u) [Ring R] (x : Unitization ℤ R) :
    x = unitalIntegerProjector R x + unitalRingProjector R x := by
  apply (NonunitalK0.unitizationUnitalEquiv R).injective
  rw [map_add]
  change (NonunitalK0.unitizationUnitalEquiv R) x =
    (NonunitalK0.unitizationUnitalEquiv R)
      ((NonunitalK0.unitizationUnitalEquiv R).symm (NonunitalK0.augmentation R x, 0)) +
    (NonunitalK0.unitizationUnitalEquiv R)
      ((NonunitalK0.unitizationUnitalEquiv R).symm (0, NonunitalK0.evaluation R x))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  simp [NonunitalK0.unitizationUnitalEquiv_apply]

private theorem unitalSplit_orthogonal (R : Type u) [Ring R] (x y : Unitization ℤ R) :
    unitalIntegerProjector R x * unitalRingProjector R y = 0 := by
  apply (NonunitalK0.unitizationUnitalEquiv R).injective
  rw [map_mul, map_zero]
  change (NonunitalK0.unitizationUnitalEquiv R)
      ((NonunitalK0.unitizationUnitalEquiv R).symm (NonunitalK0.augmentation R x, 0)) *
    (NonunitalK0.unitizationUnitalEquiv R)
      ((NonunitalK0.unitizationUnitalEquiv R).symm (0, NonunitalK0.evaluation R y)) = 0
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  simp

private theorem unitalSplit_orthogonal_reverse (R : Type u) [Ring R] (x y : Unitization ℤ R) :
    unitalRingProjector R x * unitalIntegerProjector R y = 0 := by
  apply (NonunitalK0.unitizationUnitalEquiv R).injective
  rw [map_mul, map_zero]
  change (NonunitalK0.unitizationUnitalEquiv R)
      ((NonunitalK0.unitizationUnitalEquiv R).symm (0, NonunitalK0.evaluation R x)) *
    (NonunitalK0.unitizationUnitalEquiv R)
      ((NonunitalK0.unitizationUnitalEquiv R).symm (NonunitalK0.augmentation R y, 0)) = 0
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  simp

theorem augmentation_unitalRingInclusion (R : Type u) [Ring R] :
    (NonunitalK0.augmentation R).toNonUnitalRingHom.comp (unitalRingInclusion R) = 0 := by
  ext r
  change NonunitalK0.augmentation R (unitalRingInclusion R r) = 0
  rw [unitalRingInclusion_apply, NonunitalK0.augmentation_apply]

theorem evaluation_unitalRingInclusion (R : Type u) [Ring R] :
    (NonunitalK0.evaluation R).toNonUnitalRingHom.comp (unitalRingInclusion R) =
      NonUnitalRingHom.id R := by
  ext r
  change NonunitalK0.evaluation R (unitalRingInclusion R r) = r
  rw [unitalRingInclusion_apply, NonunitalK0.evaluation_apply]
  simp

/-- The augmentation kernel of a unital ring is its original projective-module K₀. -/
def unitalEquiv (R : Type u) [Ring R] : NonunitalK0 R ≃+ RingK0 R where
  toFun x := RingK0.mapNonUnitalRingHom (NonunitalK0.evaluation R).toNonUnitalRingHom x.val
  invFun x := ⟨RingK0.mapNonUnitalRingHom (unitalRingInclusion R) x, by
    change FGProjectiveCat.scalarExtensionK0 (NonunitalK0.augmentation R)
      (RingK0.mapNonUnitalRingHom (unitalRingInclusion R) x) = 0
    rw [← RingK0.mapNonUnitalRingHom_toNonUnitalRingHom (NonunitalK0.augmentation R)]
    change ((RingK0.mapNonUnitalRingHom (NonunitalK0.augmentation R).toNonUnitalRingHom).comp
      (RingK0.mapNonUnitalRingHom (unitalRingInclusion R))) x = 0
    rw [← RingK0.mapNonUnitalRingHom_comp, augmentation_unitalRingInclusion,
      RingK0.mapNonUnitalRingHom_zero]
    rfl⟩
  left_inv x := by
    apply Subtype.ext
    have hh := DFunLike.congr_fun
      (RingK0.mapNonUnitalRingHom_add_of_orthogonal
        (unitalIntegerProjector R) (unitalRingProjector R)
        (NonUnitalRingHom.id (Unitization ℤ R))
        (unitalSplit_apply R) (unitalSplit_orthogonal R) (unitalSplit_orthogonal_reverse R)) x.val
    rw [RingK0.mapNonUnitalRingHom_id] at hh
    change x.val = RingK0.mapNonUnitalRingHom (unitalIntegerProjector R) x.val +
      RingK0.mapNonUnitalRingHom (unitalRingProjector R) x.val at hh
    have hz : RingK0.mapNonUnitalRingHom (unitalIntegerProjector R) x.val = 0 := by
      change RingK0.mapNonUnitalRingHom
        ((unitalIntegerComplement R).comp (NonunitalK0.augmentation R).toNonUnitalRingHom) x.val = 0
      rw [RingK0.mapNonUnitalRingHom_comp]
      change RingK0.mapNonUnitalRingHom (unitalIntegerComplement R)
        (RingK0.mapNonUnitalRingHom (NonunitalK0.augmentation R).toNonUnitalRingHom x.val) = 0
      rw [RingK0.mapNonUnitalRingHom_toNonUnitalRingHom]
      rw [x.property, map_zero]
    rw [hz, zero_add] at hh
    change RingK0.mapNonUnitalRingHom (unitalRingInclusion R)
      (RingK0.mapNonUnitalRingHom (NonunitalK0.evaluation R).toNonUnitalRingHom x.val) = x.val
    rw [← AddMonoidHom.comp_apply, ← RingK0.mapNonUnitalRingHom_comp]
    exact hh.symm
  right_inv x := by
    change RingK0.mapNonUnitalRingHom (NonunitalK0.evaluation R).toNonUnitalRingHom
      (RingK0.mapNonUnitalRingHom (unitalRingInclusion R) x) = x
    rw [← AddMonoidHom.comp_apply, ← RingK0.mapNonUnitalRingHom_comp,
      evaluation_unitalRingInclusion, RingK0.mapNonUnitalRingHom_id]
    rfl
  map_add' x y := map_add _ x.val y.val


/-- The inverse unital comparison is the actual projective map of the original inclusion. -/
@[simp]
theorem unitalEquiv_symm_val (R : Type u) [Ring R] (x : RingK0 R) :
    ((unitalEquiv R).symm x).val = RingK0.mapNonUnitalRingHom (unitalRingInclusion R) x :=
  rfl

/-- The forward comparison uses the original unital evaluation ring map. -/
theorem unitalEquiv_apply (R : Type u) [Ring R] (x : NonunitalK0 R) :
    unitalEquiv R x = FGProjectiveCat.scalarExtensionK0 (evaluation R) x.val := by
  change RingK0.mapNonUnitalRingHom (evaluation R).toNonUnitalRingHom x.val = _
  rw [RingK0.mapNonUnitalRingHom_toNonUnitalRingHom]

/-- A unital input class maps through the actual nonunital coefficient inclusion
of the target's unitization, including genuinely nonunital targets. -/
theorem map_unitalEquiv_symm_val {R : Type u} {I : Type v}
    [Ring R] [NonUnitalRing I] (f : R →ₙ+* I) (x : RingK0 R) :
    (map f ((unitalEquiv R).symm x)).val =
      RingK0.mapNonUnitalRingHom ((inclusion I).comp f) x := by
  rw [map_val, unitalEquiv_symm_val]
  rw [← RingK0.mapNonUnitalRingHom_toNonUnitalRingHom (unitizationMap f)]
  calc
    _ = RingK0.mapNonUnitalRingHom
        ((unitizationMap f).toNonUnitalRingHom.comp (unitalRingInclusion R)) x :=
      by
        rw [RingK0.mapNonUnitalRingHom_toNonUnitalRingHom]
        exact RingK0.scalarExtensionK0_mapNonUnitalRingHom
          (unitalRingInclusion R) (unitizationMap f) x
    _ = _ := by
      congr 2
      apply NonUnitalRingHom.ext
      intro r
      change unitizationMap f (unitalRingInclusion R r) = inclusion I (f r)
      rw [unitalRingInclusion_apply, inclusion_apply]
      apply Unitization.ext
      · rw [unitizationMap_fst]
      · rw [unitizationMap_snd]

/-- The original unital comparison is natural even for nonunital maps of its inputs. -/
theorem map_unitalEquiv_symm {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →ₙ+* S) (x : RingK0 R) :
    map f ((unitalEquiv R).symm x) =
      (unitalEquiv S).symm (RingK0.mapNonUnitalRingHom f x) := by
  apply Subtype.ext
  rw [map_unitalEquiv_symm_val, unitalEquiv_symm_val,
    unitalRingInclusion_eq_inclusion, RingK0.mapNonUnitalRingHom_comp]
  rfl

end NonunitalK0
end AlgebraicKTheory
