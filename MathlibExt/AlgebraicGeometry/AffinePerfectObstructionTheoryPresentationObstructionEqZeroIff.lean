/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Vanishing of presentation obstructions and square-zero lifts

The obstruction of a presentation theory vanishes exactly when the algebra map lifts across
a square-zero extension.

Reference: Behrend--Fantechi, *The intrinsic normal cone*, §4,
https://arxiv.org/abs/alg-geom/9601010.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted

open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
open _root_.Algebra.Extension
open MvPolynomial

private theorem transfer {k B : Type} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} {G : Algebra.Generators k B (Fin n)} (T : PresentationTheory G)
    {M : Type} [AddCommGroup M] [Module B M]
    (α : G.toExtension.Cotangent →ₗ[B] M)
    (u : (Fin T.model.zeroRank → B) →ₗ[B] M)
    (hu : u ∘ₗ T.model.differential = α ∘ₗ T.comparison.negative) :
    ∃ v : G.toExtension.CotangentSpace →ₗ[B] M,
      v ∘ₗ G.toExtension.cotangentComplex = α := by
  let r := G.toExtension.cotangentComplex.coprod T.comparison.degreeZero
  let l := α.coprod u
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨q, hq⟩ := T.bijectiveZero.2 ((LinearMap.range G.toExtension.cotangentComplex).mkQ z)
    obtain ⟨y, rfl⟩ := (LinearMap.range T.model.differential).mkQ_surjective q
    change Submodule.Quotient.mk (T.comparison.degreeZero y) = Submodule.Quotient.mk z at hq
    obtain ⟨x, hx⟩ := (Submodule.Quotient.eq _).mp hq
    refine ⟨(-x, y), ?_⟩
    change G.toExtension.cotangentComplex (-x) + T.comparison.degreeZero y = z
    rw [map_neg, hx]
    abel
  have hl : LinearMap.ker r ≤ LinearMap.ker l := by
    rintro ⟨x, y⟩ hxy
    change G.toExtension.cotangentComplex x + T.comparison.degreeZero y = 0 at hxy
    have hy : (LinearMap.range T.model.differential).mkQ y = 0 := by
      apply T.bijectiveZero.1
      rw [map_zero]
      change Submodule.Quotient.mk (T.comparison.degreeZero y) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨-x, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_right hxy).symm⟩
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
    have hz : x + T.comparison.negative a ∈ LinearMap.ker G.toExtension.cotangentComplex := by
      change G.toExtension.cotangentComplex (x + T.comparison.negative a) = 0
      rw [map_add, ← LinearMap.comp_apply, T.comparison.comm, LinearMap.comp_apply, ha]
      exact hxy
    obtain ⟨b, hb⟩ := T.surjectiveNegative ⟨x + T.comparison.negative a, hz⟩
    have hb' : T.comparison.negative b = x + T.comparison.negative a := congrArg Subtype.val hb
    have hα : α (x + T.comparison.negative a) = 0 := by
      rw [← hb', ← LinearMap.comp_apply, ← hu, LinearMap.comp_apply]
      exact (congrArg u b.2).trans (map_zero u)
    change α x + u y = 0
    rw [← ha, ← LinearMap.comp_apply, hu, LinearMap.comp_apply, ← map_add]
    exact hα
  refine ⟨r.liftOfSurjective hr ⟨l, hl⟩, ?_⟩
  ext x
  simpa [r, l] using LinearMap.equivOfSurjective_apply hr hl (m := (x, 0))

private theorem lift_of_factor {k B : Type} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} {G : Algebra.Generators k B (Fin n)}
    {A : Type} [CommRing A] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    (Q : Algebra.Extension.{0} k A) (squareZero : Q.ker ^ 2 = ⊥)
    (h : Algebra.Extension.Hom G.toExtension Q)
    (v : G.toExtension.CotangentSpace →ₗ[B] Q.Cotangent)
    (hv : v ∘ₗ G.toExtension.cotangentComplex = Cotangent.map h) :
    HasLift (B := B) Q := by
  classical
  let c : Fin n → Q.ker := fun i =>
    (Cotangent.mk_surjective (v (G.cotangentSpaceBasis i))).choose
  have hc (i : Fin n) : Cotangent.mk (c i) = v (G.cotangentSpaceBasis i) :=
    (Cotangent.mk_surjective (v (G.cotangentSpaceBasis i))).choose_spec
  let f : G.toExtension.Ring →ₐ[k] Q.Ring := aeval (fun i => h.toAlgHom (X i) - c i)
  have hf : (IsScalarTower.toAlgHom k Q.Ring A).comp f =
      (IsScalarTower.toAlgHom k B A).comp (IsScalarTower.toAlgHom k G.toExtension.Ring B) := by
    apply MvPolynomial.algHom_ext
    intro i
    change algebraMap Q.Ring A (f (X i)) =
      algebraMap B A (algebraMap G.toExtension.Ring B (X i))
    dsimp only [f]
    erw [aeval_X]
    rw [map_sub, (c i).2, sub_zero]
    exact h.algebraMap_toRingHom _
  let g : G.toExtension.Hom Q := Hom.ofAlgHom f hf
  have hsub : h.sub g = v := by
    apply G.cotangentSpaceBasis.ext
    intro i
    conv_lhs => rw [G.cotangentSpaceBasis_apply]
    erw [Hom.sub_one_tmul]
    rw [← hc]
    congr 1
    apply Subtype.ext
    change h.toAlgHom (X i) - f (X i) = (c i).1
    dsimp only [f]
    erw [aeval_X]
    exact sub_sub_cancel _ _
  have hg : Cotangent.map g = 0 := by
    have he := Cotangent.map_sub_map h g
    rw [hsub, hv] at he
    exact (sub_eq_self.mp he)
  have hk : RingHom.ker (IsScalarTower.toAlgHom k G.toExtension.Ring B).toRingHom ≤
      RingHom.ker f.toRingHom := by
    intro x hx
    have hm := LinearMap.congr_fun hg (Cotangent.mk ⟨x, hx⟩)
    change Cotangent.mk (P := Q) ⟨f x, _⟩ = 0 at hm
    have hz := (Cotangent.mk_eq_zero_iff _).mp hm
    simpa [squareZero] using hz
  let l := AlgHom.liftOfSurjective (IsScalarTower.toAlgHom k G.toExtension.Ring B)
    G.toExtension.algebraMap_surjective f hk
  refine ⟨l, ?_⟩
  ext b
  obtain ⟨p, rfl⟩ := G.toExtension.algebraMap_surjective b
  change algebraMap Q.Ring A (l ((IsScalarTower.toAlgHom k G.toExtension.Ring B) p)) = _
  dsimp only [l]
  erw [AlgHom.liftOfSurjective_apply]
  exact AlgHom.congr_fun hf p

private theorem factor_of_lift {k B : Type} [Field k] [CommRing B] [Algebra k B]
    {n : ℕ} {G : Algebra.Generators k B (Fin n)}
    {A : Type} [CommRing A] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    (Q : Algebra.Extension.{0} k A) (h : Algebra.Extension.Hom G.toExtension Q)
    (hl : HasLift (B := B) Q) :
    ∃ v : G.toExtension.CotangentSpace →ₗ[B] Q.Cotangent,
      v ∘ₗ G.toExtension.cotangentComplex = Cotangent.map h := by
  obtain ⟨l, hl⟩ := hl
  let g : G.toExtension.Hom Q := Hom.ofAlgHom
    (l.comp (IsScalarTower.toAlgHom k G.toExtension.Ring B)) (by
      rw [← AlgHom.comp_assoc, hl])
  have hg : Cotangent.map g = 0 := by
    ext x
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    rw [Cotangent.map_mk]
    change Cotangent.mk (P := Q) ⟨l (algebraMap G.toExtension.Ring B x), _⟩ = 0
    have hx : algebraMap G.toExtension.Ring B x = 0 := x.2
    simp only [hx, map_zero]
    exact map_zero Cotangent.mk
  refine ⟨h.sub g, ?_⟩
  rw [← Cotangent.map_sub_map, hg, sub_zero]

open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes in
/-- For a perfect obstruction theory relative to the naive cotangent complex of a presentation
`G` of `B` and a square-zero extension `Q` of a `B`-algebra `A`, the obstruction attached to a
morphism of extensions from `G` to `Q` vanishes exactly when `B → A` lifts to `Q`
(Behrend--Fantechi, Theorem 4.5, affine presentation form). -/
public theorem presentation_obstruction_eq_zero_iff
    {k B : Type} [Field k] [CommRing B] [Algebra k B] {n : ℕ}
    {G : Algebra.Generators k B (Fin n)} (T : PresentationTheory G)
    {A : Type} [CommRing A] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    (Q : Algebra.Extension.{0} k A) (_squareZero : Q.ker ^ 2 = ⊥)
    (h : Algebra.Extension.Hom G.toExtension Q) :
    obstruction T.model Q h T.comparison = 0 ↔ HasLift (B := B) Q := by
  constructor
  · intro ho
    obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero _).mp ho
    obtain ⟨v, hv⟩ := transfer T (Cotangent.map h) u hu
    exact lift_of_factor Q _squareZero h v hv
  · intro hl
    obtain ⟨v, hv⟩ := factor_of_lift Q h hl
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨v ∘ₗ T.comparison.degreeZero, ?_⟩
    change (v ∘ₗ T.comparison.degreeZero) ∘ₗ T.model.differential =
      Cotangent.map h ∘ₗ T.comparison.negative
    rw [LinearMap.comp_assoc, ← T.comparison.comm, ← LinearMap.comp_assoc, hv]

end WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted
