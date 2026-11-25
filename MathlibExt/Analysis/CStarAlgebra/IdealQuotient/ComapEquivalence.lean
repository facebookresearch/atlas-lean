/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Star-algebra equivalences on canonical comap quotients

Descend an actual ambient star-algebra equivalence through a two-sided
star subalgebra using the existing quotient maps and module quotients.
The algebraic construction needs no completeness, C-star laws, target
closedness or quotient norm data. Its canonical closed-ideal specialization
preserves the existing quotient norm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NonUnitalStarSubalgebra.Quotient

universe u v

namespace NonUnitalStarSubalgebra

section NormedStar

variable {D : Type u} {E : Type v}
  [NonUnitalNormedRing D] [StarRing D] [NormedSpace ℂ D]
  [IsScalarTower ℂ D D] [SMulCommClass ℂ D D] [StarModule ℂ D]
  [NonUnitalNormedRing E] [StarRing E] [NormedSpace ℂ E]
  [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] [StarModule ℂ E]

omit [IsScalarTower ℂ D D] [SMulCommClass ℂ D D] [StarModule ℂ D]
  [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] [StarModule ℂ E] in
/-- **Preimage of a two-sided star subalgebra.** Let `D,E` be nonunital normed complex star algebras,
let `e : D ≃ E` be a complex star-algebra equivalence, and let `T ⊆ E` be a two-sided nonunital star
subalgebra. The preimage `e⁻¹(T)` is a two-sided star subalgebra of `D`. -/
theorem quotientEquivComap_isTwoSided
    (e : D ≃⋆ₐ[ℂ] E) (T : NonUnitalStarSubalgebra ℂ E) [T.IsTwoSided] :
    (comap e.toNonUnitalStarAlgHom T).IsTwoSided := by
  constructor
  · intro a x hx
    change e x ∈ T at hx
    change e (a * x) ∈ T
    rw [map_mul]
    exact IsTwoSided.mul_mem_left (e a) hx
  · intro x hx a
    change e x ∈ T at hx
    change e (x * a) ∈ T
    rw [map_mul]
    exact IsTwoSided.mul_mem_right hx (e a)

/-- **Quotient equivalence induced by an ambient equivalence.** Let `D,E` be nonunital normed complex
star algebras, let `e : D ≃ E` be a complex star-algebra equivalence, and let `T ⊆ E` be a two-sided
nonunital star subalgebra. The equivalence induces a complex star-algebra equivalence `D/e⁻¹(T) ≃
E/T`. -/
noncomputable def quotientEquivComap
    (e : D ≃⋆ₐ[ℂ] E) (T : NonUnitalStarSubalgebra ℂ E) [T.IsTwoSided] :
    let S := comap e.toNonUnitalStarAlgHom T;
    letI : S.IsTwoSided := quotientEquivComap_isTwoSided e T;
    S.Quotient ≃⋆ₐ[ℂ] T.Quotient := by
  let S := comap e.toNonUnitalStarAlgHom T
  let : S.IsTwoSided := quotientEquivComap_isTwoSided e T
  have hForward : Set.MapsTo e.toNonUnitalStarAlgHom S T := by
    intro x hx
    exact hx
  have hBackward : Set.MapsTo e.symm.toNonUnitalStarAlgHom T S := by
    intro y hy
    change y ∈ T at hy
    change e (e.symm y) ∈ T
    simpa only [e.apply_symm_apply] using hy
  let f : S.Quotient →⋆ₙₐ[ℂ] T.Quotient :=
    Quotient.map S T e.toNonUnitalStarAlgHom hForward
  let g : T.Quotient →⋆ₙₐ[ℂ] S.Quotient :=
    Quotient.map T S e.symm.toNonUnitalStarAlgHom hBackward
  let mkS : D →⋆ₙₐ[ℂ] S.Quotient := Quotient.mk S
  let mkT : E →⋆ₙₐ[ℂ] T.Quotient := Quotient.mk T
  have hf (x : D) : f (mkS x) = mkT (e x) :=
    Quotient.map_mk S T e.toNonUnitalStarAlgHom hForward x
  have hg (y : E) : g (mkT y) = mkS (e.symm y) :=
    Quotient.map_mk T S e.symm.toNonUnitalStarAlgHom hBackward y
  have hLeft (q : S.Quotient) : g (f q) = q := by
    refine Submodule.Quotient.induction_on (p := quotientSubmodule S) q ?_
    intro x
    calc
      g (f (mkS x)) = g (mkT (e x)) := congrArg (fun r : T.Quotient => g r) (hf x)
      _ = mkS (e.symm (e x)) := hg (e x)
      _ = mkS x := congrArg (fun z : D => mkS z) (e.symm_apply_apply x)
  have hRight (q : T.Quotient) : f (g q) = q := by
    refine Submodule.Quotient.induction_on (p := quotientSubmodule T) q ?_
    intro y
    calc
      f (g (mkT y)) = f (mkS (e.symm y)) := congrArg (fun r : S.Quotient => f r) (hg y)
      _ = mkT (e (e.symm y)) := hf (e.symm y)
      _ = mkT y := congrArg (fun z : E => mkT z) (e.apply_symm_apply y)
  exact
    { toFun := f
      invFun := g
      left_inv := hLeft
      right_inv := hRight
      map_mul' := map_mul f
      map_add' := map_add f
      map_star' := map_star f
      map_smul' := map_smul f }

omit [IsScalarTower ℂ D D] [SMulCommClass ℂ D D] [StarModule ℂ D]
  [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] [StarModule ℂ E] in
/-- **Forward formula for quotient transport.** Let `D,E` be nonunital normed complex star algebras, let
`e : D ≃ E` be a complex star-algebra equivalence, and let `T ⊆ E` be a two-sided nonunital star
subalgebra. The induced equivalence sends the class of `d ∈ D` to the class of `e(d)` in `E/T`. -/
theorem quotientEquivComap_mk
    (e : D ≃⋆ₐ[ℂ] E) (T : NonUnitalStarSubalgebra ℂ E) [T.IsTwoSided] :
    let S := comap e.toNonUnitalStarAlgHom T;
    letI : S.IsTwoSided := quotientEquivComap_isTwoSided e T;
    ∀ x : D, quotientEquivComap e T (Quotient.mk S x) = Quotient.mk T (e x) := by
  dsimp only
  intro x
  rfl

omit [IsScalarTower ℂ D D] [SMulCommClass ℂ D D] [StarModule ℂ D]
  [IsScalarTower ℂ E E] [SMulCommClass ℂ E E] [StarModule ℂ E] in
/-- **Inverse formula for quotient transport.** Let `D,E` be nonunital normed complex star algebras, let
`e : D ≃ E` be a complex star-algebra equivalence, and let `T ⊆ E` be a two-sided nonunital star
subalgebra. The inverse induced equivalence sends the class of `x ∈ E` to the class of `e⁻¹(x)` in
`D/e⁻¹(T)`. -/
theorem quotientEquivComap_symm_mk
    (e : D ≃⋆ₐ[ℂ] E) (T : NonUnitalStarSubalgebra ℂ E) [T.IsTwoSided] :
    let S := comap e.toNonUnitalStarAlgHom T;
    letI : S.IsTwoSided := quotientEquivComap_isTwoSided e T;
    ∀ y : E, (quotientEquivComap e T).symm (Quotient.mk T y) =
      Quotient.mk S (e.symm y) := by
  dsimp only
  intro y
  rfl

end NormedStar

end NonUnitalStarSubalgebra

private theorem quotientEquivComap_canonical_norm
    {D : Type u} {E : Type v}
    [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E]
    (e : D ≃⋆ₐ[ℂ] E) (J : ClosedStarIdeal E) :
    let I := ClosedStarIdeal.comap e.toNonUnitalStarAlgHom J;
    let S := NonUnitalStarSubalgebra.comap e.toNonUnitalStarAlgHom J.carrier;
    let hCarrier : I.carrier = S := rfl;
    letI : J.carrier.IsTwoSided := J.isTwoSided;
    letI : S.IsTwoSided := NonUnitalStarSubalgebra.quotientEquivComap_isTwoSided e J.carrier;
    let hClosed : IsClosed (S : Set D) :=
      (by simpa only [hCarrier] using I.isClosed);
    letI : IsClosed (S : Set D) := hClosed;
    letI : NonUnitalCStarAlgebra S.Quotient :=
      NonUnitalStarSubalgebra.Quotient.nonUnitalCStarAlgebra S;
    letI : NonUnitalCStarAlgebra J.Quotient := J.quotientCStarAlgebra;
    ∀ q : S.Quotient,
      ‖NonUnitalStarSubalgebra.quotientEquivComap e J.carrier q‖ = ‖q‖ := by
  let I := ClosedStarIdeal.comap e.toNonUnitalStarAlgHom J
  let S := NonUnitalStarSubalgebra.comap e.toNonUnitalStarAlgHom J.carrier
  have hCarrier : I.carrier = S := rfl
  let : J.carrier.IsTwoSided := J.isTwoSided
  let : S.IsTwoSided := NonUnitalStarSubalgebra.quotientEquivComap_isTwoSided e J.carrier
  have hClosed : IsClosed (S : Set D) := by
    simpa only [hCarrier] using I.isClosed
  let : IsClosed (S : Set D) := hClosed
  let : NonUnitalCStarAlgebra S.Quotient :=
    NonUnitalStarSubalgebra.Quotient.nonUnitalCStarAlgebra S
  let : NonUnitalCStarAlgebra J.Quotient := J.quotientCStarAlgebra
  dsimp only
  intro q
  let qEquiv : S.Quotient ≃⋆ₐ[ℂ] J.Quotient :=
    NonUnitalStarSubalgebra.quotientEquivComap e J.carrier
  exact NonUnitalStarAlgHom.norm_map qEquiv qEquiv.injective q
