/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel.Matrix
public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtension

/-!
# Original scalar extension of finite-row idempotent ranges

Entrywise coefficient mapping retains the existing finite-row Karoubi carrier.
The original integral balanced scalar extension of a range has the actual
mapped range as its canonical S-module coordinates. Products remain ordered;
the rings and the idempotent matrices need not be commutative or invertible.
-/

public section

noncomputable section

open CategoryTheory
open ModuleCat.RingHomScalarExtension
open scoped Matrix

universe uR uS

namespace FGProjectiveCat.IdempotentModel

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Map the original idempotent matrix while retaining the existing natural-rank model. -/
@[expose, reducible]
def mapObject (f : R →+* S) (P : IdempotentModel R) : IdempotentModel S where
  X := P.X
  p := (rowHomEquiv S P.X P.X).symm ((rowHomEquiv R P.X P.X P.p).map f)
  idem := by
    apply (rowHomEquiv S P.X P.X).injective
    rw [(equivalence_characteristic S).2.2.1]
    simp only [AddEquiv.apply_symm_apply]
    have h := congrArg (fun e => f.mapMatrix e)
      ((equivalence_characteristic R).2.2.2.1 P)
    simpa only [map_mul, RingHom.mapMatrix_apply] using h

/-- The rank is the same literal natural number. -/
@[simp]
theorem mapObject_rank (f : R →+* S) (P : IdempotentModel R) :
    (mapObject f P).X = P.X := rfl

/-- The actual idempotent row matrix is mapped entrywise. -/
theorem mapObject_matrix (f : R →+* S) (P : IdempotentModel R) :
    rowHomEquiv S P.X P.X (mapObject f P).p =
      (rowHomEquiv R P.X P.X P.p).map f :=
  AddEquiv.apply_symm_apply _ _

private theorem range_fixed (P : IdempotentModel R) (x : range R P) :
    (rowHomEquiv R P.X P.X P.p).toLinearMapRight' x.val = x.val := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy, ← Matrix.toLinearMapRight'_mul_apply,
    (equivalence_characteristic R).2.2.2.1 P]

/-- The actual image of a standard basis row under the original idempotent. -/
def matrixRow (P : IdempotentModel R) (i : Fin P.X) : range R P :=
  ⟨(rowHomEquiv R P.X P.X P.p).toLinearMapRight' (Pi.single i 1),
    ⟨Pi.single i 1, rfl⟩⟩

/-- Its original coordinate is the corresponding idempotent matrix entry. -/
@[simp]
theorem matrixRow_val (P : IdempotentModel R) (i j : Fin P.X) :
    (matrixRow P i).val j = rowHomEquiv R P.X P.X P.p i j := by
  simp [matrixRow, Matrix.toLinearMapRight'_apply]

private def coordinates (f : R →+* S) (P : IdempotentModel R) :
    tensor f (range R P) →ₗ[S] (Fin P.X → S) :=
  LinearMap.pi (fun j => coefficient f
    ((LinearMap.proj j).comp (range R P).subtype))

private theorem coordinates_pure (f : R →+* S) (P : IdempotentModel R)
    (s : S) (p : range R P) (j : Fin P.X) :
    coordinates f P (pure f (range R P) s p) j = s * f (p.val j) := by
  change coefficient f ((LinearMap.proj j).comp (range R P).subtype)
    (pure f (range R P) s p) = _
  rw [coefficient_pure]
  rfl

private theorem coordinates_fixed (f : R →+* S) (P : IdempotentModel R)
    (x : tensor f (range R P)) :
    (rowHomEquiv S P.X P.X (mapObject f P).p).toLinearMapRight'
      (coordinates f P x) = coordinates f P x := by
  have h : (rowHomEquiv S P.X P.X (mapObject f P).p).toLinearMapRight'.comp
      (coordinates f P) = coordinates f P := by
    apply linearMap_ext f (range R P)
    intro s p
    ext j
    have hc : coordinates f P (pure f (range R P) s p) =
        (fun i => s * f (p.val i)) := funext (coordinates_pure f P s p)
    simp only [LinearMap.comp_apply]
    rw [hc, mapObject_matrix]
    simp only [Matrix.toLinearMapRight'_apply, Matrix.vecMul_apply,
      dotProduct, Matrix.col_apply, Matrix.map_apply]
    have hp := congrFun (range_fixed P p) j
    change (∑ i, p.val i * rowHomEquiv R P.X P.X P.p i j) = p.val j at hp
    calc
      (∑ i, (s * f (p.val i)) * f (rowHomEquiv R P.X P.X P.p i j)) =
          s * f (∑ i, p.val i * rowHomEquiv R P.X P.X P.p i j) := by
            simp only [map_sum, map_mul, Finset.mul_sum, mul_assoc]
      _ = s * f (p.val j) := congrArg (fun r => s * f r) hp
  exact LinearMap.congr_fun h x

private def forward (f : R →+* S) (P : IdempotentModel R) :
    tensor f (range R P) →ₗ[S] range S (mapObject f P) :=
  (coordinates f P).codRestrict _ (fun x => ⟨coordinates f P x, coordinates_fixed f P x⟩)

private def backward (f : R →+* S) (P : IdempotentModel R) :
    range S (mapObject f P) →ₗ[S] tensor f (range R P) where
  toFun x := ∑ i : Fin P.X, x.val i • pure f (range R P) 1 (matrixRow P i)
  map_add' x y := by
    simp only [Submodule.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' s x := by
    change (∑ i, (s * x.val i) • pure f (range R P) 1 (matrixRow P i)) =
      s • (∑ i : Fin P.X, x.val i • pure f (range R P) 1 (matrixRow P i))
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_smul s (x.val i) _

private theorem reconstruction (P : IdempotentModel R) (p : range R P) :
    (∑ i, p.val i • matrixRow P i) = p := by
  apply Subtype.ext
  ext j
  have hp := congrFun (range_fixed P p) j
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, matrixRow_val, Matrix.toLinearMapRight'_apply, Matrix.vecMul_apply,
    dotProduct, Matrix.col_apply] using hp

private theorem forward_comp_backward (f : R →+* S) (P : IdempotentModel R) :
    (forward f P).comp (backward f P) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  ext j
  change coefficient f ((LinearMap.proj j).comp (range R P).subtype)
    (∑ i : Fin P.X, x.val i • pure f (range R P) 1 (matrixRow P i)) = x.val j
  simp only [map_sum, map_smul, coefficient_pure, one_mul]
  change (∑ i : Fin P.X, x.val i * f ((matrixRow P i).val j)) = x.val j
  simp only [matrixRow_val]
  have hx := congrFun (range_fixed (mapObject f P) x) j
  change (rowHomEquiv S P.X P.X (mapObject f P).p).toLinearMapRight' x.val j =
    x.val j at hx
  rw [mapObject_matrix] at hx
  simpa only [Matrix.toLinearMapRight'_apply, Matrix.vecMul_apply,
    dotProduct, Matrix.col_apply, Matrix.map_apply] using hx

private theorem backward_comp_forward (f : R →+* S) (P : IdempotentModel R) :
    (backward f P).comp (forward f P) = LinearMap.id := by
  apply linearMap_ext f (range R P)
  intro s p
  change (∑ i, coordinates f P (pure f (range R P) s p) i •
      pure f (range R P) 1 (matrixRow P i)) =
    pure f (range R P) s p
  simp only [coordinates_pure]
  calc
    _ = ∑ i, pure f (range R P) (s * f (p.val i)) (matrixRow P i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_pure, mul_one]
    _ = ∑ i, pure f (range R P) s (p.val i • matrixRow P i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact pure_balance f (range R P) (p.val i) s (matrixRow P i)
    _ = pure f (range R P) s (∑ i, p.val i • matrixRow P i) := by rw [map_sum]
    _ = pure f (range R P) s p := congrArg (pure f (range R P) s) (reconstruction P p)

/-- Original balanced scalar extension of the range is the actual mapped idempotent range. -/
def rangeScalarExtensionLinearEquiv (f : R →+* S) (P : IdempotentModel R) :
    tensor f (range R P) ≃ₗ[S] range S (mapObject f P) :=
  LinearEquiv.ofLinearMap (forward f P) (backward f P)
    (forward_comp_backward f P) (backward_comp_forward f P)

/-- The forward map retains the ordered original pure coordinates. -/
theorem rangeScalarExtensionLinearEquiv_pure (f : R →+* S) (P : IdempotentModel R)
    (s : S) (p : range R P) (j : Fin P.X) :
    (rangeScalarExtensionLinearEquiv f P (pure f (range R P) s p)).val j =
      s * f (p.val j) :=
  coordinates_pure f P s p j

private theorem rangeScalarExtensionLinearEquiv_symm_computed
    (f : R →+* S) (P : IdempotentModel R)
    (x : range S (mapObject f P)) :
    (rangeScalarExtensionLinearEquiv f P).symm x =
      ∑ i : Fin P.X, x.val i • pure f (range R P) 1 (matrixRow P i) := rfl

/-- The inverse is the actual finite sum of unit pure classes of idempotent rows. -/
theorem rangeScalarExtensionLinearEquiv_symm (f : R →+* S) (P : IdempotentModel R)
    (x : range S (mapObject f P)) :
    (rangeScalarExtensionLinearEquiv f P).symm x =
      ∑ i : Fin P.X, x.val i • pure f (range R P) 1 (matrixRow P i) :=
  rangeScalarExtensionLinearEquiv_symm_computed f P x

private def nativeCarrier (f : R →+* S) (A : FGProjectiveCat.{uR} R) :
    (ringScalarExtension f).obj A ≃ₗ[S] tensor f A :=
  (UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S ((scalarExtension f).obj A)).trans
    (scalarExtensionCarrierLinearEquiv f A)

private theorem nativeCarrier_map (f : R →+* S)
    {A B : FGProjectiveCat.{uR} R} (g : A ⟶ B) :
    (nativeCarrier f B).toLinearMap.comp ((ringScalarExtension f).map g).hom.hom =
      (linearMap f g.hom.hom).comp (nativeCarrier f A).toLinearMap := by
  apply LinearMap.ext
  intro x
  let x0 : UniverseEquivalence.shrinkObject.{uS,uR} S ((scalarExtension f).obj A) := x
  change scalarExtensionCarrierLinearEquiv f B
      (UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S ((scalarExtension f).obj B)
        (((UniverseEquivalence.shrinkFunctor.{uS,uR} S).map
          ((scalarExtension f).map g)).hom.hom x0)) =
    linearMap f g.hom.hom
      (scalarExtensionCarrierLinearEquiv f A
        (UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S ((scalarExtension f).obj A) x0))
  have hm := UniverseEquivalence.shrinkFunctor_map_apply.{uS,uR} S
    ((scalarExtension f).map g) x0
  have hc := congrArg
    (UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S ((scalarExtension f).obj B)) hm
  have hs := LinearEquiv.apply_symm_apply
    (UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S ((scalarExtension f).obj B))
    (((scalarExtension f).map g).hom.hom
      (UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S ((scalarExtension f).obj A) x0))
  exact (congrArg (scalarExtensionCarrierLinearEquiv f B) (hc.trans hs)).trans
    (LinearMap.congr_fun (scalarExtensionCarrierLinearEquiv_naturality f g)
      (UniverseEquivalence.shrinkLinearEquiv.{uS,uR} S ((scalarExtension f).obj A) x0))

/-- The earned carrier dictionary of the same original ring-universe scalar extension. -/
def scalarRangeCarrierLinearEquiv (f : R →+* S) (P : IdempotentModel R) :
    (ringScalarExtension f).obj ((equivalence R).functor.obj P) ≃ₗ[S]
      tensor f (range R P) := by
  let A := FGProjectiveCat.of (R := R) (range R P)
  let h : (equivalence R).functor.obj P ≅ A := eqToIso (equivalence_obj R P)
  exact (FGProjectiveCat.isoToLinearEquiv ((ringScalarExtension f).mapIso h)).trans
    (nativeCarrier f A)

/-- Original scalar extension of the original range realization is the actual mapped range
realization, for arbitrary associative rings. -/
def scalarExtensionIso (f : R →+* S) (P : IdempotentModel R) :
    (ringScalarExtension f).obj ((equivalence R).functor.obj P) ≅
      (equivalence S).functor.obj (mapObject f P) :=
  FGProjectiveCat.isoOfLinearEquiv
    ((scalarRangeCarrierLinearEquiv f P).trans
      ((rangeScalarExtensionLinearEquiv f P).trans
        (FGProjectiveCat.isoToLinearEquiv
          (eqToIso (equivalence_obj S (mapObject f P)))).symm))

private theorem scalarExtensionIso_pure_computed (f : R →+* S) (P : IdempotentModel R)
    (s : S) (p : range R P) (j : Fin P.X) :
    (FGProjectiveCat.isoToLinearEquiv (eqToIso (equivalence_obj S (mapObject f P)))
      (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P)
        ((scalarRangeCarrierLinearEquiv f P).symm (pure f (range R P) s p)))).val j =
      s * f (p.val j) := by
  change ((FGProjectiveCat.isoToLinearEquiv
    (eqToIso (equivalence_obj S (mapObject f P))))
    ((FGProjectiveCat.isoToLinearEquiv
      (eqToIso (equivalence_obj S (mapObject f P)))).symm
      (rangeScalarExtensionLinearEquiv f P
        (scalarRangeCarrierLinearEquiv f P
          ((scalarRangeCarrierLinearEquiv f P).symm (pure f (range R P) s p)))))).val j = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact rangeScalarExtensionLinearEquiv_pure f P s p j

/-- The whole original object isomorphism sends the original pure class to `s*f(pⱼ)`. -/
theorem scalarExtensionIso_pure (f : R →+* S) (P : IdempotentModel R)
    (s : S) (p : range R P) (j : Fin P.X) :
    (FGProjectiveCat.isoToLinearEquiv (eqToIso (equivalence_obj S (mapObject f P)))
      (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P)
        ((scalarRangeCarrierLinearEquiv f P).symm (pure f (range R P) s p)))).val j =
      s * f (p.val j) :=
  scalarExtensionIso_pure_computed f P s p j

private theorem scalarExtensionIso_inverse_computed (f : R →+* S) (P : IdempotentModel R)
    (x : range S (mapObject f P)) :
    scalarRangeCarrierLinearEquiv f P
      ((FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P)).symm
        ((FGProjectiveCat.isoToLinearEquiv
          (eqToIso (equivalence_obj S (mapObject f P)))).symm x)) =
      (rangeScalarExtensionLinearEquiv f P).symm x := by
  change scalarRangeCarrierLinearEquiv f P
    ((scalarRangeCarrierLinearEquiv f P).symm
      ((rangeScalarExtensionLinearEquiv f P).symm
        (FGProjectiveCat.isoToLinearEquiv (eqToIso (equivalence_obj S (mapObject f P)))
          ((FGProjectiveCat.isoToLinearEquiv
            (eqToIso (equivalence_obj S (mapObject f P)))).symm x)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The original object inverse returns the same finite sum of original unit pure classes. -/
theorem scalarExtensionIso_inverse (f : R →+* S) (P : IdempotentModel R)
    (x : range S (mapObject f P)) :
    scalarRangeCarrierLinearEquiv f P
      ((FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P)).symm
        ((FGProjectiveCat.isoToLinearEquiv
          (eqToIso (equivalence_obj S (mapObject f P)))).symm x)) =
      ∑ i : Fin P.X, x.val i • pure f (range R P) 1 (matrixRow P i) :=
  (scalarExtensionIso_inverse_computed f P x).trans
    (rangeScalarExtensionLinearEquiv_symm f P x)

/-- The actual quotient scalar-extension comparison; two-sidedness earns the quotient ring. -/
def quotientScalarExtensionIso (I : Ideal R) [I.IsTwoSided] (P : IdempotentModel R) :
    (ringScalarExtension (Ideal.Quotient.mk I)).obj ((equivalence R).functor.obj P) ≅
      (equivalence (R ⧸ I)).functor.obj (mapObject (Ideal.Quotient.mk I) P) :=
  scalarExtensionIso (Ideal.Quotient.mk I) P

private theorem corner_matrix {P Q : IdempotentModel R} (g : P ⟶ Q) :
    rowHomEquiv R P.X P.X P.p * rowHomEquiv R P.X Q.X g.f *
      rowHomEquiv R Q.X Q.X Q.p = rowHomEquiv R P.X Q.X g.f := by
  have h := (equivalence_characteristic R).2.2.2.2.2.2.2.1 P Q g
  rw [h.1, h.2]

/-- Map an original rectangular corner matrix in the same existing idempotent model. -/
def mapHom (f : R →+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) :
    mapObject f P ⟶ mapObject f Q :=
  homOfMatrix S ((rowHomEquiv R P.X Q.X g.f).map f) (by
    change rowHomEquiv S P.X P.X (mapObject f P).p *
      (rowHomEquiv R P.X Q.X g.f).map f *
      rowHomEquiv S Q.X Q.X (mapObject f Q).p = _
    rw [mapObject_matrix, mapObject_matrix]
    rw [← Matrix.map_mul, ← Matrix.map_mul, corner_matrix g])

private theorem mapHom_matrix_computed
    (f : R →+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) :
    rowHomEquiv S P.X Q.X (mapHom f g).f = (rowHomEquiv R P.X Q.X g.f).map f := by
  change rowHomEquiv S (mapObject f P).X (mapObject f Q).X (mapHom f g).f = _
  unfold mapHom
  exact homOfMatrix_matrix _ _ _

/-- The target corner matrix is the literal entrywise coefficient map. -/
@[simp]
theorem mapHom_matrix (f : R →+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) :
    rowHomEquiv S P.X Q.X (mapHom f g).f = (rowHomEquiv R P.X Q.X g.f).map f :=
  mapHom_matrix_computed f g

private def rangeHom {P Q : IdempotentModel R} (g : P ⟶ Q) :
    range R P →ₗ[R] range R Q :=
  ((eqToIso (equivalence_obj R P)).inv ≫ (equivalence R).functor.map g ≫
    (eqToIso (equivalence_obj R Q)).hom).hom.hom

private theorem rangeHom_val {P Q : IdempotentModel R} (g : P ⟶ Q) (p : range R P) :
    (rangeHom g p).val = (rowHomEquiv R P.X Q.X g.f).toLinearMapRight' p.val :=
  (equivalence_characteristic R).2.2.2.2.2.2.2.2.2.2.1 P Q g p

private theorem forward_pure_val (f : R →+* S) (P : IdempotentModel R)
    (s : S) (p : range R P) (j : Fin P.X) :
    (forward f P (pure f (range R P) s p)).val j = s * f (p.val j) :=
  coordinates_pure f P s p j

private theorem raw_naturality (f : R →+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) :
    (forward f Q).comp (linearMap f (rangeHom g)) =
      (rangeHom (mapHom f g)).comp (forward f P) := by
  apply linearMap_ext f (range R P)
  intro s p
  apply Subtype.ext
  refine funext (fun (j : Fin Q.X) => ?_)
  simp only [LinearMap.comp_apply, linearMap_pure]
  change (forward f Q (pure f (range R Q) s (rangeHom g p))).val j =
    (rangeHom (mapHom f g) (forward f P (pure f (range R P) s p))).val j
  rw [forward_pure_val, rangeHom_val, rangeHom_val]
  change s * f ((rowHomEquiv R P.X Q.X g.f).toLinearMapRight' p.val j) =
    (rowHomEquiv S P.X Q.X (mapHom f g).f).toLinearMapRight'
      (forward f P (pure f (range R P) s p)).val j
  rw [mapHom_matrix]
  have hfp : (forward f P (pure f (range R P) s p)).val =
      (fun i => s * f (p.val i)) := funext (forward_pure_val f P s p)
  rw [hfp]
  simp only [Matrix.toLinearMapRight'_apply, Matrix.vecMul_apply,
    dotProduct, Matrix.col_apply, Matrix.map_apply]
  simp only [map_sum, map_mul, Finset.mul_sum, mul_assoc]

private theorem scalarRangeCarrier_map (f : R →+* S) {P Q : IdempotentModel R}
    (g : P ⟶ Q) :
    (scalarRangeCarrierLinearEquiv f Q).toLinearMap.comp
        ((ringScalarExtension f).map ((equivalence R).functor.map g)).hom.hom =
      (linearMap f (rangeHom g)).comp (scalarRangeCarrierLinearEquiv f P).toLinearMap := by
  let hP := eqToIso (equivalence_obj R P)
  let hQ := eqToIso (equivalence_obj R Q)
  let gR := hP.inv ≫ (equivalence R).functor.map g ≫ hQ.hom
  have hc : (equivalence R).functor.map g ≫ hQ.hom = hP.hom ≫ gR := by
    dsimp only [gR]
    simp only [Iso.hom_inv_id_assoc]
  have hmap := congrArg (ringScalarExtension f).map hc
  rw [Functor.map_comp, Functor.map_comp] at hmap
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun h => h.hom.hom x) hmap
  change ((ringScalarExtension f).map hQ.hom).hom.hom
      (((ringScalarExtension f).map ((equivalence R).functor.map g)).hom.hom x) =
    ((ringScalarExtension f).map gR).hom.hom
      (((ringScalarExtension f).map hP.hom).hom.hom x) at hx
  change nativeCarrier f (FGProjectiveCat.of (R := R) (range R Q))
      (((ringScalarExtension f).map hQ.hom).hom.hom
        (((ringScalarExtension f).map ((equivalence R).functor.map g)).hom.hom x)) =
    linearMap f (rangeHom g)
      (nativeCarrier f (FGProjectiveCat.of (R := R) (range R P))
        (((ringScalarExtension f).map hP.hom).hom.hom x))
  rw [hx]
  exact LinearMap.congr_fun (nativeCarrier_map f gR)
    (((ringScalarExtension f).map hP.hom).hom.hom x)

private def targetCarrier (P : IdempotentModel R) :
    (equivalence R).functor.obj P ≃ₗ[R] range R P :=
  FGProjectiveCat.isoToLinearEquiv (eqToIso (equivalence_obj R P))

private theorem targetCarrier_map {P Q : IdempotentModel R} (g : P ⟶ Q) :
    (targetCarrier Q).toLinearMap.comp ((equivalence R).functor.map g).hom.hom =
      (rangeHom g).comp (targetCarrier P).toLinearMap := by
  apply LinearMap.ext
  intro x
  change targetCarrier Q (((equivalence R).functor.map g).hom.hom x) =
    targetCarrier Q (((equivalence R).functor.map g).hom.hom
      ((targetCarrier P).symm (targetCarrier P x)))
  rw [LinearEquiv.symm_apply_apply]

private theorem scalarExtensionIso_forward (f : R →+* S) (P : IdempotentModel R)
    (x : (ringScalarExtension f).obj ((equivalence R).functor.obj P)) :
    targetCarrier (mapObject f P)
        (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P) x) =
      forward f P (scalarRangeCarrierLinearEquiv f P x) := by
  change targetCarrier (mapObject f P)
    ((targetCarrier (mapObject f P)).symm
      (forward f P (scalarRangeCarrierLinearEquiv f P x))) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- The whole original scalar-extension isomorphism is natural for every original rectangular
corner morphism, without an invertibility hypothesis. -/
theorem scalarExtensionIso_naturality (f : R →+* S) {P Q : IdempotentModel R}
    (g : P ⟶ Q) :
    (ringScalarExtension f).map ((equivalence R).functor.map g) ≫
        (scalarExtensionIso f Q).hom =
      (scalarExtensionIso f P).hom ≫ (equivalence S).functor.map (mapHom f g) := by
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (targetCarrier (mapObject f Q)).injective
  change targetCarrier (mapObject f Q)
      (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f Q)
        (((ringScalarExtension f).map ((equivalence R).functor.map g)).hom.hom x)) =
    targetCarrier (mapObject f Q)
      (((equivalence S).functor.map (mapHom f g)).hom.hom
        (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P) x))
  rw [scalarExtensionIso_forward]
  have hs := LinearMap.congr_fun (scalarRangeCarrier_map f g) x
  change scalarRangeCarrierLinearEquiv f Q
      (((ringScalarExtension f).map ((equivalence R).functor.map g)).hom.hom x) =
    linearMap f (rangeHom g) (scalarRangeCarrierLinearEquiv f P x) at hs
  rw [hs]
  have hr := LinearMap.congr_fun (raw_naturality f g) (scalarRangeCarrierLinearEquiv f P x)
  change forward f Q (linearMap f (rangeHom g) (scalarRangeCarrierLinearEquiv f P x)) =
    rangeHom (mapHom f g) (forward f P (scalarRangeCarrierLinearEquiv f P x)) at hr
  rw [hr]
  have ht := LinearMap.congr_fun (targetCarrier_map (mapHom f g))
    (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P) x)
  change targetCarrier (mapObject f Q)
      (((equivalence S).functor.map (mapHom f g)).hom.hom
        (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P) x)) =
    rangeHom (mapHom f g)
      (targetCarrier (mapObject f P)
        (FGProjectiveCat.isoToLinearEquiv (scalarExtensionIso f P) x)) at ht
  rw [ht, scalarExtensionIso_forward]

end FGProjectiveCat.IdempotentModel

end
