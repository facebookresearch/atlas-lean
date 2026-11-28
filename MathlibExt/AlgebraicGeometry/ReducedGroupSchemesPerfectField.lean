/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricallyReduced
public import MathlibExt.CategoryTheory.Monoidal.GrpObjOfMono
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Reduced schemes and reduced group schemes over a perfect field

For a scheme `X`, the reduction `X_red` is the closed subscheme `X.nilradical.subscheme` cut out
by the nilradical, with its closed immersion `X.nilradical.subschemeι` into `X`.

* `AlgebraicGeometry.Scheme.isReduced_subscheme_radical`: a closed subscheme cut out by a radical
  ideal sheaf is reduced, so `X_red` is reduced.
* `AlgebraicGeometry.Scheme.Hom.liftNilradical`: a morphism from a reduced scheme to `X` factors
  through `X_red`.

Let `k` be a perfect field.

* `AlgebraicGeometry.isReduced_pullback_of_perfectField`: the fibre product `X ×_k Y` of two
  reduced `k`-schemes is reduced (Stacks project, Varieties, Lemma 33.6.7 (4), Tag 035Z).
* `AlgebraicGeometry.grpObjNilradicalSubscheme` and
  `AlgebraicGeometry.isMonHom_nilradicalSubschemeι`: for a group scheme `G` over `k`, `G_red` is
  a group scheme over `k` and its closed immersion into `G` is a homomorphism (Stacks project,
  Groupoid Schemes, Lemma 39.7.6, Tag 047R).
* `AlgebraicGeometry.smooth_of_grpObj_of_isReduced_of_perfectField`: a reduced group scheme
  locally of finite type over `k` is smooth over `k` (Stacks project, Groupoid Schemes,
  Lemma 39.8.4, Tag 047P, there in characteristic `p > 0`).

The product statement reduces to affine schemes, where it is
`Algebra.isReduced_tensorProduct_of_perfectField_of_isReduced`. For Tag 047R, the unit, the
multiplication and the inverse of `G` restricted to `G_red` have reduced sources (`Spec k`,
`G_red ×_k G_red` and `G_red`), so they factor through `G_red`; this is the hint given in the
Stacks project. Smoothness combines
`AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField` (Varieties,
Lemma 33.6.3, Tag 020I) with Mathlib's `AlgebraicGeometry.smooth_of_grpObj` for geometrically
reduced group schemes; it does not follow the proof of Lemma 39.8.4, which uses differentials.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}}

/-- The nilradical of `X` is contained in the kernel of any morphism from a reduced scheme. -/
lemma nilradical_le_ker_of_isReduced [IsReduced Y] (g : Y ⟶ X) : X.nilradical ≤ g.ker := by
  rw [Hom.ker, IdealSheafData.le_ofIdeals_iff]
  intro U x hx
  rw [← IdealSheafData.radical_bot, IdealSheafData.radical_ideal,
    IdealSheafData.ideal_bot] at hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker]
  refine IsNilpotent.eq_zero ⟨n, ?_⟩
  rw [← map_pow]
  simp only [Pi.bot_apply, Ideal.mem_bot] at hn
  simp [hn]

/-- The closed subscheme cut out by a radical ideal sheaf is reduced. -/
instance isReduced_subscheme_radical (I : X.IdealSheafData) : IsReduced I.radical.subscheme := by
  have (U : X.affineOpens) : IsReduced (I.radical.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (.of (Γ(X, U) ⧸ I.radical.ideal U)))
    have : _root_.IsReduced (Γ(X, U) ⧸ I.radical.ideal U) := by
      rw [← Ideal.isRadical_iff_quotient_reduced, IdealSheafData.radical_ideal]
      exact Ideal.radical_isRadical _
    infer_instance
  exact @IsReduced.of_openCover _ I.radical.subschemeCover.openCover this

/-- The reduction `X_red = X.nilradical.subscheme` of `X` is reduced. -/
instance isReduced_nilradical_subscheme : IsReduced X.nilradical.subscheme :=
  isReduced_subscheme_radical ⊥

/-- A morphism from a reduced scheme to `X` factors through the reduction
`X.nilradical.subscheme` of `X`. -/
noncomputable def Hom.liftNilradical (g : Y ⟶ X) (hY : IsReduced Y) :
    Y ⟶ X.nilradical.subscheme :=
  g.toImage ≫ IdealSheafData.inclusion (nilradical_le_ker_of_isReduced g)

@[reassoc (attr := simp)]
lemma Hom.liftNilradical_subschemeι (g : Y ⟶ X) (hY : IsReduced Y) :
    g.liftNilradical hY ≫ X.nilradical.subschemeι = g := by
  simp [Hom.liftNilradical]

end Scheme

variable {k : Type u} [Field k] [PerfectField k]

/-- The fibre product over `Spec k` of two reduced affine schemes is reduced. -/
private lemma isReduced_pullback_spec {R S : CommRingCat.{u}} (f : Spec R ⟶ Spec (.of k))
    (g : Spec S ⟶ Spec (.of k)) (hR : IsReduced (Spec R)) (hS : IsReduced (Spec S)) :
    IsReduced (pullback f g) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom, ψ.hom]
  have : _root_.IsReduced R := (affine_isReduced_iff R).mp hR
  have : _root_.IsReduced S := (affine_isReduced_iff S).mp hS
  have : _root_.IsReduced (R ⊗[k] S) :=
    Algebra.isReduced_tensorProduct_of_perfectField_of_isReduced k R S
  have : IsReduced (Spec (.of (R ⊗[k] S))) := (affine_isReduced_iff _).mpr ‹_›
  exact isReduced_of_isOpenImmersion (pullbackSpecIso k R S).hom

/-- **Products of reduced schemes over a perfect field.** Let `k` be a perfect field and `X`, `Y`
reduced schemes over `k`. Then `X ×_k Y` is reduced.

This is the Stacks project, Varieties, Lemma 33.6.7 (4) (Tag 035Z): "If `k` is perfect and `X` and
`Y` are reduced, then `X ×_k Y` is reduced." -/
theorem isReduced_pullback_of_perfectField {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (g : Y ⟶ Spec (.of k)) [IsReduced X] [IsReduced Y] : IsReduced (pullback f g) := by
  let 𝒰 := Scheme.Pullback.openCoverOfLeftRight X.affineCover Y.affineCover f g
  have (i : 𝒰.I₀) : IsReduced (𝒰.X i) :=
    isReduced_pullback_spec (X.affineCover.f i.1 ≫ f) (Y.affineCover.f i.2 ≫ g)
      (@isReduced_of_isOpenImmersion _ _ (X.affineCover.f i.1) (X.affineCover.map_prop i.1) _)
      (@isReduced_of_isOpenImmersion _ _ (Y.affineCover.f i.2) (Y.affineCover.map_prop i.2) _)
  exact IsReduced.of_openCover _ 𝒰

section GroupScheme

variable {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)]

/-- The closed immersion `G_red ⟶ G` of the reduction of `G`, as a morphism over `Spec k`. -/
noncomputable abbrev nilradicalSubschemeι :
    Over.mk (G.nilradical.subschemeι ≫ f) ⟶ Over.mk f :=
  Over.homMk G.nilradical.subschemeι

instance : Mono (nilradicalSubschemeι f) := Over.mono_homMk _

/-- The unit of `G_red`. -/
noncomputable def nilradicalSubschemeOne :
    𝟙_ (Over (Spec (.of k))) ⟶ Over.mk (G.nilradical.subschemeι ≫ f) :=
  Over.homMk (Scheme.Hom.liftNilradical (X := G) η[Over.mk f].left
    (show IsReduced (Spec (.of k)) from inferInstance)) (by
      simp only [Over.mk_hom, Scheme.Hom.liftNilradical_subschemeι_assoc]
      exact Over.w η[Over.mk f])

/-- The multiplication of `G_red`, defined because `G_red ×_k G_red` is reduced. -/
noncomputable def nilradicalSubschemeMul :
    Over.mk (G.nilradical.subschemeι ≫ f) ⊗ Over.mk (G.nilradical.subschemeι ≫ f) ⟶
      Over.mk (G.nilradical.subschemeι ≫ f) :=
  Over.homMk (Scheme.Hom.liftNilradical (X := G)
      (Y := pullback (G.nilradical.subschemeι ≫ f) (G.nilradical.subschemeι ≫ f))
      ((nilradicalSubschemeι f ⊗ₘ nilradicalSubschemeι f) ≫ μ[Over.mk f]).left
      (isReduced_pullback_of_perfectField _ _)) (by
      simp only [Over.mk_hom, Scheme.Hom.liftNilradical_subschemeι_assoc]
      exact Over.w ((nilradicalSubschemeι f ⊗ₘ nilradicalSubschemeι f) ≫ μ[Over.mk f]))

/-- The inverse of `G_red`. -/
noncomputable def nilradicalSubschemeInv :
    Over.mk (G.nilradical.subschemeι ≫ f) ⟶ Over.mk (G.nilradical.subschemeι ≫ f) :=
  Over.homMk (Scheme.Hom.liftNilradical (X := G) (Y := G.nilradical.subscheme)
      (nilradicalSubschemeι f ≫ ι[Over.mk f]).left inferInstance) (by
      simp only [Over.mk_hom, Scheme.Hom.liftNilradical_subschemeι_assoc]
      exact Over.w (nilradicalSubschemeι f ≫ ι[Over.mk f]))

omit [PerfectField k] in
lemma nilradicalSubschemeOne_ι :
    nilradicalSubschemeOne f ≫ nilradicalSubschemeι f = η[Over.mk f] := by
  ext1; simp [nilradicalSubschemeOne]

lemma nilradicalSubschemeMul_ι :
    nilradicalSubschemeMul f ≫ nilradicalSubschemeι f =
      (nilradicalSubschemeι f ⊗ₘ nilradicalSubschemeι f) ≫ μ[Over.mk f] := by
  ext1; simp [nilradicalSubschemeMul]

omit [PerfectField k] in
lemma nilradicalSubschemeInv_ι :
    nilradicalSubschemeInv f ≫ nilradicalSubschemeι f =
      nilradicalSubschemeι f ≫ ι[Over.mk f] := by
  ext1; simp [nilradicalSubschemeInv]

/-- **The reduction of a group scheme over a perfect field is a group scheme.** Let `k` be a
perfect field and `G` a group scheme over `k`. Then its reduction `G_red = G.nilradical.subscheme`
is a group scheme over `k`, for the unit, multiplication and inverse of `G` restricted to `G_red`;
with `AlgebraicGeometry.isMonHom_nilradicalSubschemeι`, the closed immersion `G_red ⟶ G` is a
homomorphism.

This is the Stacks project, Groupoid Schemes, Lemma 39.7.6 (Tag 047R): "Let `G` be a group scheme
over a perfect field `k`. Then the reduction `G_red` of `G` is a closed subgroup scheme of `G`." -/
noncomputable instance grpObjNilradicalSubscheme :
    GrpObj (Over.mk (G.nilradical.subschemeι ≫ f)) :=
  GrpObj.ofMono (nilradicalSubschemeι f) (nilradicalSubschemeOne f) (nilradicalSubschemeMul f)
    (nilradicalSubschemeInv f) (nilradicalSubschemeOne_ι f) (nilradicalSubschemeMul_ι f)
    (nilradicalSubschemeInv_ι f)

/-- The closed immersion `G_red ⟶ G` is a homomorphism of group schemes over `k`, for the group
structure `AlgebraicGeometry.grpObjNilradicalSubscheme` (Stacks project, Tag 047R). -/
instance isMonHom_nilradicalSubschemeι : IsMonHom (nilradicalSubschemeι f) :=
  GrpObj.isMonHom_ofMono _ _ _ _ (nilradicalSubschemeOne_ι f) (nilradicalSubschemeMul_ι f)
    (nilradicalSubschemeInv_ι f)

/-- **Reduced group schemes over a perfect field are smooth.** Let `k` be a perfect field and
`G` a group scheme over `k` (`f : G ⟶ Spec k` with a group object structure on `Over.mk f`)
which is locally of finite type over `k`. If `G` is reduced, then `f` is smooth.

This is the Stacks project, Groupoid Schemes, Lemma 39.8.4 (Tag 047P): "Let `k` be a perfect
field of characteristic `p > 0` (see Lemma 39.8.2 for the characteristic zero case). Let `G` be a
locally algebraic group scheme over `k`. If `G` is reduced then the structure morphism
`G → Spec(k)` is smooth, i.e., `G` is a smooth group scheme." Locally algebraic means locally of
finite type over `k` (Section 39.8). The statement here makes no assumption on the
characteristic. -/
theorem smooth_of_grpObj_of_isReduced_of_perfectField [LocallyOfFiniteType f] [IsReduced G] :
    Smooth f :=
  have : GeometricallyReduced f := GeometricallyReduced.of_isReduced_of_perfectField f
  smooth_of_grpObj f

end GroupScheme

end AlgebraicGeometry
