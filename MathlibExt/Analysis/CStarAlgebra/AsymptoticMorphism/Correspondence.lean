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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.AsymptoticAlgebra
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Bounds

/-!
# Raw asymptotic families and the actual asymptotic-algebra correspondence

The derived neutral orbit bound packages every raw time orbit in BCF.
The four asymptotic defects then give an actual nonunital star homomorphism
into the existing closed-ray Cb/C0 quotient. Equality is precisely strict
equivalence, and the existing quotient-surjective set lift proves surjectivity.

This is the strict quotient, not a homotopy quotient. No coefficient continuity,
unitality, separability, extra bound or exact-zero hypothesis is imposed.
The carrier, norm, quotient projection and strict setoid are the existing ones.

Reference: Blackadar, K-Theory for Operator Algebras (1998), 25.1.3–25.1.4(a).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace AsymptoticMorphism

universe uA uB

attribute [local instance] _root_.AsymptoticAlgebra.cStarAlgebra

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- An actual raw time orbit bundled using the derived neutral bound. -/
@[no_expose]
def orbitBCF (φ : AsymptoticMorphism A B) (a : A) : AsymptoticTime →ᵇ B where
  toFun t := φ t a
  continuous_toFun := by
    simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
      _root_.AsymptoticMorphism.continuous_orbit φ a
  map_bounded' := by
    obtain ⟨C, hC⟩ := (_root_.AsymptoticMorphism.norm_bounded_and_eventually_contractive φ a).1
    refine ⟨C + C, fun s t => ?_⟩
    exact (dist_le_norm_add_norm (φ s a) (φ t a)).trans
      (add_le_add (hC s) (hC t))

/-- Bundling changes no pointwise value or time parameter. -/
@[simp]
theorem orbitBCF_apply (φ : AsymptoticMorphism A B)
    (a : A) (t : AsymptoticTime) : orbitBCF φ a t = φ t a := by
  rfl

/-- The actual quotient homomorphism of a raw asymptotic family. -/
@[no_expose]
def toHom (φ : AsymptoticMorphism A B) : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B where
  toFun a := _root_.AsymptoticAlgebra.quotientMap B (orbitBCF φ a)
  map_zero' := by
    apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
    have ht : Tendsto (fun t : AsymptoticTime => φ t (0 : A)) atTop (nhds (0 : B)) :=
      _root_.AsymptoticMorphism.zero_tendsto φ
    exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
      simp only [orbitBCF_apply])
  map_add' := by
    intro a b
    have h :
        _root_.AsymptoticAlgebra.quotientMap B
          (orbitBCF φ (a + b) - (orbitBCF φ a + orbitBCF φ b)) = 0 := by
      apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
      have ht : Tendsto (fun t : AsymptoticTime =>
          φ t (a + b) - (φ t a + φ t b)) atTop (nhds (0 : B)) := by
        simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
          _root_.AsymptoticMorphism.add_defect_tendsto φ a b
      exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
        simp only [BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.add_apply, orbitBCF_apply])
    rw [map_sub, map_add, sub_eq_zero] at h
    exact h
  map_smul' := by
    intro z a
    have h :
        _root_.AsymptoticAlgebra.quotientMap B
          (orbitBCF φ (z • a) - z • orbitBCF φ a) = 0 := by
      apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
      have ht : Tendsto (fun t : AsymptoticTime =>
          φ t (z • a) - z • φ t a) atTop (nhds (0 : B)) := by
        simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
          _root_.AsymptoticMorphism.smul_defect_tendsto φ z a
      exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
        simp only [BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.smul_apply, orbitBCF_apply])
    rw [map_sub, map_smul, sub_eq_zero] at h
    exact h
  map_mul' := by
    intro a b
    have h :
        _root_.AsymptoticAlgebra.quotientMap B
          (orbitBCF φ (a * b) - orbitBCF φ a * orbitBCF φ b) = 0 := by
      apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
      have ht : Tendsto (fun t : AsymptoticTime =>
          φ t (a * b) - φ t a * φ t b) atTop (nhds (0 : B)) := by
        simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
          _root_.AsymptoticMorphism.mul_defect_tendsto φ a b
      exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
        simp only [BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.mul_apply, orbitBCF_apply])
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact h
  map_star' := by
    intro a
    have h :
        _root_.AsymptoticAlgebra.quotientMap B
          (orbitBCF φ (star a) - star (orbitBCF φ a)) = 0 := by
      apply (_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff _).2
      have ht : Tendsto (fun t : AsymptoticTime =>
          φ t (star a) - star (φ t a)) atTop (nhds (0 : B)) := by
        simpa only [_root_.AsymptoticMorphism.toFun_eq_coe] using
          _root_.AsymptoticMorphism.star_defect_tendsto φ a
      exact ht.congr' (Filter.Eventually.of_forall fun (t : AsymptoticTime) => by
        simp only [BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.star_apply, orbitBCF_apply])
    rw [map_sub, map_star, sub_eq_zero] at h
    exact h

/-- The printed quotient class of the actual time orbit. -/
@[simp]
theorem toHom_apply (φ : AsymptoticMorphism A B) (a : A) :
    toHom φ a = _root_.AsymptoticAlgebra.quotientMap B (orbitBCF φ a) := by
  rfl

/-- The kernel criterion recovers EXACT strict equivalence, not homotopy. -/
theorem toHom_eq_iff (φ ψ : AsymptoticMorphism A B) :
    toHom φ = toHom ψ ↔ StrictlyEquivalent φ ψ := by
  constructor
  · intro h a
    have hq := DFunLike.congr_fun h a
    rw [toHom_apply, toHom_apply] at hq
    have ht := (_root_.AsymptoticAlgebra.quotientMap_eq_iff
      (orbitBCF φ a) (orbitBCF ψ a)).1 hq
    simpa only [orbitBCF_apply] using ht
  · intro h
    apply NonUnitalStarAlgHom.ext
    intro a
    apply (_root_.AsymptoticAlgebra.quotientMap_eq_iff _ _).2
    simpa only [orbitBCF_apply] using h a

/-- The actual neutral set lift maps back to the original quotient hom. -/
theorem toHom_ofHom (ρ : A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) :
    toHom (_root_.AsymptoticAlgebra.ofHom ρ) = ρ := by
  apply NonUnitalStarAlgHom.ext
  intro a
  change _root_.AsymptoticAlgebra.quotientMap B
      (orbitBCF (_root_.AsymptoticAlgebra.ofHom ρ) a) = ρ a
  have horbit : orbitBCF (_root_.AsymptoticAlgebra.ofHom ρ) a =
      Classical.choose (_root_.AsymptoticAlgebra.quotientMap_surjective B (ρ a)) := by
    apply BoundedContinuousFunction.ext
    intro t
    rw [orbitBCF_apply, _root_.AsymptoticAlgebra.ofHom_apply]
  rw [horbit]
  exact Classical.choose_spec (_root_.AsymptoticAlgebra.quotientMap_surjective B (ρ a))

/-- The induced map on the ACTUAL existing strict-equivalence quotient. -/
def strictClassToHom :
    Quotient (strictSetoid A B) → (A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) :=
  Quotient.lift toHom (fun φ ψ h => (toHom_eq_iff φ ψ).2 h)

/-- The strict-equivalence class map has its original representative formula. -/
@[simp]
theorem strictClassToHom_mk (φ : AsymptoticMorphism A B) :
    strictClassToHom (Quotient.mk (strictSetoid A B) φ) = toHom φ := by
  rfl

/-- The literal strict correspondence, using the separate derived orbit bound.
It does not equate strict and homotopy classes. -/
def strictClassEquiv :
    Quotient (strictSetoid A B) ≃ (A →⋆ₙₐ[ℂ] AsymptoticAlgebra B) :=
  Equiv.ofBijective strictClassToHom ⟨
    by
      intro q r
      refine Quotient.inductionOn₂ q r ?_
      intro φ ψ h
      rw [strictClassToHom_mk, strictClassToHom_mk] at h
      exact Quotient.sound ((toHom_eq_iff φ ψ).1 h),
    by
      intro ρ
      exact ⟨Quotient.mk (strictSetoid A B) (_root_.AsymptoticAlgebra.ofHom ρ),
        toHom_ofHom ρ⟩⟩

/-- The concrete bijection is the quotient hom of the original raw family. -/
@[simp]
theorem strictClassEquiv_mk (φ : AsymptoticMorphism A B) :
    strictClassEquiv (Quotient.mk (strictSetoid A B) φ) = toHom φ := by
  rfl


end AsymptoticMorphism

end

end
