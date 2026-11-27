/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEtale
import Mathlib.Algebra.DualNumber

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace RelativeGroupLawEtaleTest

/-- Source-shaped consumer with the original binders: commutativity as a hypothesis on the
multiplication of points, smoothness of relative dimension `d`, and `n` a unit in the local
base ring give an étale multiplication by `n`. -/
example {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) :=
  G.etale_schemeNsmul_of_isUnit (fun t x y => hcomm t x y) d n hn

/-- Source-shaped consumer of the formally unramified step, which needs no smoothness. -/
example {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (G.schemeNsmul n) :=
  G.formallyUnramified_schemeNsmul_of_isUnit (fun t x y => hcomm t x y) n hn

/-- The statement is universe polymorphic: a consumer in a higher universe. -/
example {R : Type (u + 1)} [CommRing R] [IsLocalRing R] {A : Scheme.{u + 1}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) :=
  G.etale_schemeNsmul_of_isUnit hc d n hn

/-- Over a field of characteristic zero every positive `n` is a unit, so multiplication by
`n` on a smooth commutative group law over the field is étale. -/
example {K : Type u} [Field K] [CharZero K] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : n ≠ 0) :
    Etale (G.schemeNsmul n) :=
  G.etale_schemeNsmul_of_isUnit hc d n (by simpa using hn)

/-- Infinitesimal `n`-torsion points reducing to the identity are trivial when `n` is a unit. -/
example {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {n : ℕ}
    (hn : IsUnit (n : R)) {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f)
    (hk : Over.homMk (U := Over.mk (Spec.map φ ≫ t)) (V := Over.mk t) (Spec.map φ) rfl ≫ k =
      G.one (Spec.map φ ≫ t))
    (hnk : G.nsmul t n k = G.one t) :
    k = G.one t :=
  G.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit hn φ hφ hker t k hk hnk

/-- The lifting criterion takes exactly the triviality of infinitesimal `n`-torsion points that
`eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit` provides. -/
example {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
    (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (G.schemeNsmul n) :=
  G.formallyUnramified_schemeNsmul_of_forall_sqZero hc n fun _ _ φ hφ hker t k hk hnk =>
    G.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit hn φ hφ hker t k hk hnk

/-- The identity point over a test scheme is its structure morphism followed by the identity
section. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).left = t ≫ G.unitSection := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id t)]
  rfl

/-! ### The additive group over `ℚ` and a dual-number point -/

section AdditiveGroup

open MvPolynomial

/-- The coordinate ring `ℚ[X]` of the additive group over `ℚ`. -/
private noncomputable abbrev gaRing : CommRingCat.{0} := CommRingCat.of (MvPolynomial (Fin 1) ℚ)

/-- The structure morphism of the additive group `Spec ℚ[X]` over `Spec ℚ`. -/
private noncomputable abbrev gaStr : Spec gaRing ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (MvPolynomial (Fin 1) ℚ)))

/-- Any two morphisms to `Spec ℚ` agree. -/
private theorem toSpecRat_ext {T : Scheme.{0}} (g h : T ⟶ Spec (CommRingCat.of ℚ)) : g = h :=
  ext_to_Spec (CommRingCat.hom_ext (Subsingleton.elim _ _))

/-- The coordinate of a morphism to `Spec ℚ[X]`: the global section that the variable pulls
back to. -/
private noncomputable def coord {T : Scheme.{0}} (x : T ⟶ Spec gaRing) : Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso gaRing).inv ≫ x.appTop) (X 0)

/-- Morphisms to `Spec ℚ[X]` with the same coordinate agree. -/
private theorem eq_of_coord_eq {T : Scheme.{0}} {x y : T ⟶ Spec gaRing}
    (h : coord x = coord y) : x = y := by
  refine ext_to_Spec (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)))
  · exact DFunLike.congr_fun (Subsingleton.elim
      (((Scheme.ΓSpecIso gaRing).inv ≫ Scheme.Γ.map x.op).hom.comp C)
      (((Scheme.ΓSpecIso gaRing).inv ≫ Scheme.Γ.map y.op).hom.comp C)) r
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h

/-- The morphism to `Spec ℚ[X]` with coordinate `b`, for a test scheme over `Spec ℚ`. -/
private noncomputable def toGa {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (b : Γ(T, ⊤)) : T ⟶ Spec gaRing :=
  ΓSpec.adjunction.homEquiv T (Opposite.op gaRing)
    (CommRingCat.ofHom (eval₂Hom ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ t.appTop).hom
      fun _ => b)).op

private theorem coord_toGa {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)) (b : Γ(T, ⊤)) :
    coord (toGa t b) = b := by
  rw [coord, toGa, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  simp

private theorem coord_comp {T T' : Scheme.{0}} (ψ : T' ⟶ T) (x : T ⟶ Spec gaRing) :
    coord (ψ ≫ x) = ψ.appTop (coord x) := by
  simp only [coord, Scheme.Hom.comp_appTop]
  rfl

/-- The additive group over `ℚ`: points over a test scheme add through their coordinates. -/
private noncomputable def gaLaw : RelativeGroupLaw ℚ gaStr where
  mul t x y := Over.homMk (toGa t (coord x.left + coord y.left)) (toSpecRat_ext _ _)
  one t := Over.homMk (toGa t 0) (toSpecRat_ext _ _)
  inv t x := Over.homMk (toGa t (-coord x.left)) (toSpecRat_ext _ _)
  mul_assoc _ _ _ _ := Over.OverMorphism.ext <| eq_of_coord_eq <| by
    simp only [Over.homMk_left, coord_toGa, add_assoc]
  one_mul _ _ := Over.OverMorphism.ext <| eq_of_coord_eq <| by
    simp only [Over.homMk_left, coord_toGa, zero_add]
  mul_one _ _ := Over.OverMorphism.ext <| eq_of_coord_eq <| by
    simp only [Over.homMk_left, coord_toGa, add_zero]
  inv_mul_cancel _ _ := Over.OverMorphism.ext <| eq_of_coord_eq <| by
    simp only [Over.homMk_left, coord_toGa, neg_add_cancel]
  mul_natural _ _ ψ _ _ _ := Over.OverMorphism.ext <| eq_of_coord_eq <| by
    simp only [Over.comp_left, Over.homMk_left, coord_comp, coord_toGa, map_add]

private theorem gaLaw_isCommutative : gaLaw.IsCommutative := fun _ _ _ =>
  Over.OverMorphism.ext <| eq_of_coord_eq <| by
    simp only [gaLaw, Over.homMk_left, coord_toGa, add_comm]

/-- The additive group is smooth of relative dimension `1` over `Spec ℚ`. -/
private instance : SmoothOfRelativeDimension 1 gaStr := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)) _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr inferInstance)

/-- The dual numbers `ℚ[ε]`. -/
private abbrev dualRing : CommRingCat.{0} := CommRingCat.of (DualNumber ℚ)

/-- The square-zero thickening `ℚ[ε] → ℚ`. -/
private noncomputable abbrev dualProj : dualRing ⟶ CommRingCat.of ℚ :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom ℚ ℚ ℚ).toRingHom

/-- The structure morphism of `Spec ℚ[ε]` over `Spec ℚ`. -/
private noncomputable abbrev dualBase : Spec dualRing ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (DualNumber ℚ)))

private theorem dualProj_surjective : Function.Surjective dualProj :=
  fun q => ⟨TrivSqZeroExt.inl q, rfl⟩

private theorem ker_dualProj_sq : RingHom.ker dualProj.hom ^ 2 = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker] at hx hy
  change x.fst = 0 at hx
  change y.fst = 0 at hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

/-- `ε`, as a global section of `Spec ℚ[ε]`. -/
private noncomputable abbrev epsSection : Γ(Spec dualRing, ⊤) :=
  (Scheme.ΓSpecIso dualRing).inv DualNumber.eps

/-- The point of the additive group over `Spec ℚ[ε]` with coordinate `ε`. -/
private noncomputable def epsPoint : Over.mk dualBase ⟶ Over.mk gaStr :=
  Over.homMk (toGa dualBase epsSection) (toSpecRat_ext _ _)

private theorem appTop_dualProj_epsSection : (Spec.map dualProj).appTop epsSection = 0 := by
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality dualProj)) DualNumber.eps
  have h0 : dualProj.hom DualNumber.eps = 0 := rfl
  rw [CommRingCat.hom_comp, RingHom.comp_apply, h0, map_zero] at h
  exact h.symm

/-- `ε` reduces to the identity over `Spec ℚ`. -/
private theorem epsPoint_reduces :
    Over.homMk (U := Over.mk (Spec.map dualProj ≫ dualBase)) (V := Over.mk dualBase)
        (Spec.map dualProj) rfl ≫ epsPoint = gaLaw.one (Spec.map dualProj ≫ dualBase) :=
  Over.OverMorphism.ext <| eq_of_coord_eq <| by
    simp only [Over.comp_left, Over.homMk_left, epsPoint, gaLaw, coord_comp, coord_toGa]
    exact appTop_dualProj_epsSection

/-- `ε` is not the identity. -/
private theorem epsPoint_ne_one : epsPoint ≠ gaLaw.one dualBase := by
  intro h
  have h1 := congrArg (fun x => coord x.left) h
  simp only [epsPoint, gaLaw, Over.homMk_left, coord_toGa] at h1
  have h2 := congrArg (fun z => (Scheme.ΓSpecIso dualRing).hom z) h1
  simp only [epsSection, Iso.inv_hom_id_apply, map_zero] at h2
  exact (one_ne_zero : (1 : ℚ) ≠ 0) (by simpa using congrArg TrivSqZeroExt.snd h2)

/-- The infinitesimal-torsion lemma on a positive-dimensional group: `ε` reduces to the identity
and is not the identity, so `2 • ε` is not the identity, as `2` is a unit in `ℚ`. -/
private theorem nsmul_two_epsPoint_ne_one : gaLaw.nsmul dualBase 2 epsPoint ≠ gaLaw.one dualBase :=
  fun h => epsPoint_ne_one <| gaLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit (by simp)
    dualProj dualProj_surjective ker_dualProj_sq dualBase epsPoint epsPoint_reduces h

/-- The lifts `0` and `ε` of the identity both reduce to it, and multiplication by `2`
separates them. -/
example : gaLaw.nsmul dualBase 2 (gaLaw.one dualBase) ≠ gaLaw.nsmul dualBase 2 epsPoint := by
  rw [gaLaw.nsmul_one_point]
  exact fun h => nsmul_two_epsPoint_ne_one h.symm

/-- Multiplication by `2` on the additive group over `ℚ`, which is smooth of relative
dimension `1`, is étale. -/
example : Etale (gaLaw.schemeNsmul 2) :=
  gaLaw.etale_schemeNsmul_of_isUnit gaLaw_isCommutative 1 2 (by simp)

end AdditiveGroup

end RelativeGroupLawEtaleTest
