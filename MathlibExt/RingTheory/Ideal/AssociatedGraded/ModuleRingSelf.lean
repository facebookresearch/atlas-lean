/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.RingTheory.Ideal.AssociatedGraded.ModuleRing
public import MathlibExt.RingTheory.Ideal.AssociatedGraded.ModuleSelf
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Generators and the regular associated graded module

Let `R` be a commutative ring, `I` an ideal, and `M` an `R`-module. If `s ⊆ M` spans `M` over
`R`, the degree-zero initial forms of elements of `s` span `gr_I M` over `gr_I R`. Hence
finite generation of `M` over `R` gives finite generation of the total graded module over the
total graded ring.

For the regular module `R`, the equality `I^n R = I^n` in every degree induces a `gr_I
R`-linear equivalence `gr_I(R as a module) ≃ gr_I R`. It preserves homogeneous inclusions and
initial forms of representatives.

Reference: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped DirectSum Pointwise

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

private def associatedGradedModulePowZeroMap (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    M →ₗ[R] ↥(I ^ 0 • (⊤ : Submodule R M)) where
  toFun m := ⟨m, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def associatedGradedModuleDegreeZeroMap (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    M →ₗ[R] I.AssociatedGradedModule M :=
  (DirectSum.lof R ℕ (I.AssociatedGradedModulePiece M) 0).comp
    ((I.initialFormModule M 0).comp
      (associatedGradedModulePowZeroMap I M))

@[simp]
private theorem associatedGradedModuleDegreeZeroMap_apply
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    associatedGradedModuleDegreeZeroMap I M m =
      DirectSum.of (I.AssociatedGradedModulePiece M) 0
        (I.initialFormModule M 0 ⟨m, by simp⟩) :=
  rfl

/-- Let `R` be a commutative ring, `I` an ideal, `M` an `R`-module, and `s : Set M` with
`Submodule.span R s = ⊤`. The degree-zero images `j_0([m]_0)` for `m ∈ s` span
`I.AssociatedGradedModule M` over `I.AssociatedGraded`. Here `[m]_0` is the class in `M/IM`
and `j_0` its direct-sum inclusion. -/
theorem associatedGradedModule_span_degreeZero_generators_eq_top
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (s : Set M) (hs : Submodule.span R s = ⊤) :
    Submodule.span I.AssociatedGraded
      ((fun m ↦ DirectSum.of (I.AssociatedGradedModulePiece M) 0
        (I.initialFormModule M 0 ⟨m, by simp⟩)) '' s) = ⊤ := by
  change Submodule.span I.AssociatedGraded
    (associatedGradedModuleDegreeZeroMap I M '' s) = ⊤
  let P : Submodule I.AssociatedGraded (I.AssociatedGradedModule M) :=
    Submodule.span I.AssociatedGraded
      (associatedGradedModuleDegreeZeroMap I M '' s)
  have hgen (m : M) : associatedGradedModuleDegreeZeroMap I M m ∈ P := by
    have hm : m ∈ Submodule.span R s := by
      rw [hs]
      exact Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
        exact Submodule.subset_span
          (Set.mem_image_of_mem (associatedGradedModuleDegreeZeroMap I M) hx)
    | zero =>
        rw [map_zero]
        exact P.zero_mem
    | add x y _ _ hx hy =>
        rw [map_add]
        exact P.add_mem hx hy
    | smul r x _ hx =>
        let a : I.AssociatedGraded :=
          (algebraMap (R ⧸ I) I.AssociatedGraded :
            (R ⧸ I) →+* I.AssociatedGraded) (Ideal.Quotient.mk I r)
        have h := P.smul_mem a hx
        dsimp only [a] at h
        rw [associatedGradedModuleDegreeZeroMap_apply] at h
        rw [I.associatedGradedModule_algebraMap_smul_of M] at h
        rw [I.initialFormModule_apply, Module.Quotient.mk_smul_mk] at h
        rw [associatedGradedModuleDegreeZeroMap_apply,
          I.initialFormModule_apply]
        exact h
  apply top_unique
  intro x hx
  clear hx
  change x ∈ P
  induction x using DirectSum.induction_on with
  | zero => exact P.zero_mem
  | add x y hx hy => exact P.add_mem hx hy
  | of n q =>
      obtain ⟨z, rfl⟩ := I.initialFormModule_surjective M n q
      refine Submodule.smul_induction_on' z.2
        (p := fun z hz ↦ DirectSum.of (I.AssociatedGradedModulePiece M) n
          (I.initialFormModule M n ⟨z, hz⟩) ∈ P) ?_ ?_
      · intro r hr m _
        have h := P.smul_mem
          (DirectSum.of I.AssociatedGradedPiece n
            (I.initialForm n ⟨r, hr⟩)) (hgen m)
        rw [associatedGradedModuleDegreeZeroMap_apply] at h
        rw [I.associatedGradedModule_of_smul_of,
          I.associatedGradedModuleSMul_initialForm] at h
        convert h using 1
      · intro x hx y hy hxP hyP
        have heq : (⟨x + y, Submodule.add_mem _ hx hy⟩ :
            ↥(I ^ n • (⊤ : Submodule R M))) = ⟨x, hx⟩ + ⟨y, hy⟩ := by
          apply Subtype.ext
          rfl
        rw [heq, map_add, map_add]
        exact P.add_mem hxP hyP

/-- For an ideal `I` in a commutative ring `R` and a finitely generated `R`-module `M`, the total
associated graded module `gr_I M` is finitely generated over `gr_I R`: `Module.Finite
I.AssociatedGraded (I.AssociatedGradedModule M)`. Degree-zero initial forms of a finite
generating set of `M` generate this module. -/
noncomputable instance associatedGradedModule_finite
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Module.Finite I.AssociatedGraded (I.AssociatedGradedModule M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  apply Module.Finite.of_fg_top
  refine ⟨s.image (associatedGradedModuleDegreeZeroMap I M), ?_⟩
  rw [Finset.coe_image]
  exact I.associatedGradedModule_span_degreeZero_generators_eq_top M s hs

private theorem associatedGradedModulePieceSelfEquiv_initialFormModule
    (I : Ideal R) (n : ℕ)
    (y : ↥(I ^ n • (⊤ : Submodule R R))) :
    I.associatedGradedModulePieceSelfEquiv n
        (I.initialFormModule R n y) =
      I.initialForm n ⟨y, by simpa using y.2⟩ := by
  let x : (I ^ n : Ideal R) := ⟨y, by simpa using y.2⟩
  have hy : y = (⟨x, by simp [x.2]⟩ :
      ↥(I ^ n • (⊤ : Submodule R R))) := by
    apply Subtype.ext
    rfl
  rw [hy, I.associatedGradedModulePieceSelfEquiv_initialForm]

private theorem associatedGradedModulePieceSelfEquiv_smul
    (I : Ideal R) (m n : ℕ) (a : I.AssociatedGradedPiece m)
    (x : I.AssociatedGradedModulePiece R n) :
    I.associatedGradedModulePieceSelfEquiv (m + n)
        (I.associatedGradedModuleSMul R m n a x) =
      I.adicGradedMul m n a
        (I.associatedGradedModulePieceSelfEquiv n x) := by
  obtain ⟨r, rfl⟩ := I.initialForm_surjective m a
  obtain ⟨y, rfl⟩ := I.initialFormModule_surjective R n x
  rw [I.associatedGradedModuleSMul_initialForm,
    associatedGradedModulePieceSelfEquiv_initialFormModule,
    associatedGradedModulePieceSelfEquiv_initialFormModule]
  change I.adicSymbol (m + n) _ =
    I.adicGradedMul m n (I.adicSymbol m r) (I.adicSymbol n _)
  rw [I.adicGradedMul_symbol]
  rfl

private def associatedGradedModuleSelfEquivTotal0 (I : Ideal R) :
    I.AssociatedGradedModule R ≃ₗ[R ⧸ I] I.AssociatedGraded :=
  DirectSum.congrLinearEquiv fun n ↦
    I.associatedGradedModulePieceSelfEquiv n

@[simp]
private theorem associatedGradedModuleSelfEquivTotal0_of
    (I : Ideal R) (n : ℕ) (x : I.AssociatedGradedModulePiece R n) :
    associatedGradedModuleSelfEquivTotal0 I
        (DirectSum.of (I.AssociatedGradedModulePiece R) n x) =
      DirectSum.of I.AssociatedGradedPiece n
        (I.associatedGradedModulePieceSelfEquiv n x) := by
  rw [associatedGradedModuleSelfEquivTotal0,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_of]
  rfl

private theorem associatedGradedModuleSelfEquivTotal0_smul
    (I : Ideal R) (a : I.AssociatedGraded)
    (x : I.AssociatedGradedModule R) :
    associatedGradedModuleSelfEquivTotal0 I (a • x) =
      a * associatedGradedModuleSelfEquivTotal0 I x := by
  change associatedGradedModuleSelfEquivTotal0 I
      ((DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
        (I.AssociatedGradedModulePiece R)) a x) =
    (DirectSum.mulHom I.AssociatedGradedPiece) a
      (associatedGradedModuleSelfEquivTotal0 I x)
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add a b ha hb =>
      simp only [map_add, AddMonoidHom.add_apply, ha, hb]
  | of m a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | of n x =>
          rw [associatedGradedModuleSelfEquivTotal0_of,
            DirectSum.Gmodule.smulAddMonoidHom_apply_of_of,
            DirectSum.mulHom_of_of]
          change associatedGradedModuleSelfEquivTotal0 I
              (DirectSum.of (I.AssociatedGradedModulePiece R) (m + n)
                (I.associatedGradedModuleSMul R m n a x)) =
            DirectSum.of I.AssociatedGradedPiece (m + n)
              (I.adicGradedMul m n a
                (I.associatedGradedModulePieceSelfEquiv n x))
          rw [associatedGradedModuleSelfEquivTotal0_of,
            associatedGradedModulePieceSelfEquiv_smul]

private def associatedGradedModuleSelfMapTotal (I : Ideal R) :
    I.AssociatedGradedModule R →ₗ[I.AssociatedGraded]
      I.AssociatedGraded where
  toFun := associatedGradedModuleSelfEquivTotal0 I
  map_add' := map_add _
  map_smul' := by
    intro a x
    change associatedGradedModuleSelfEquivTotal0 I (a • x) =
      a * associatedGradedModuleSelfEquivTotal0 I x
    exact associatedGradedModuleSelfEquivTotal0_smul I a x

/-- For an ideal `I` in a commutative ring `R`, the associated graded module of the regular module
`R` is `gr_I R` as a module over itself. This is the `gr_I R`-linear equivalence
`I.AssociatedGradedModule R ≃ₗ[I.AssociatedGraded] I.AssociatedGraded`, preserving
representatives in every ideal-power degree. -/
@[no_expose]
noncomputable def associatedGradedModuleSelfEquivTotal (I : Ideal R) :
    I.AssociatedGradedModule R ≃ₗ[I.AssociatedGraded]
      I.AssociatedGraded :=
  LinearEquiv.ofBijective (associatedGradedModuleSelfMapTotal I)
    (associatedGradedModuleSelfEquivTotal0 I).bijective

/-- Let `R` be a commutative ring, `I` an ideal, `n : ℕ`, and `x ∈ I.AssociatedGradedModulePiece R
n`. If `E` is the total regular-module equivalence and `E_n` the fixed-degree equivalence,
then `E(j_n(x)) = j_n(E_n x)`, where the two `j_n` maps include the module and ring degree-`n`
pieces into their direct sums. -/
@[simp]
theorem associatedGradedModuleSelfEquivTotal_of
    (I : Ideal R) (n : ℕ) (x : I.AssociatedGradedModulePiece R n) :
    I.associatedGradedModuleSelfEquivTotal
        (DirectSum.of (I.AssociatedGradedModulePiece R) n x) =
      DirectSum.of I.AssociatedGradedPiece n
        (I.associatedGradedModulePieceSelfEquiv n x) := by
  change associatedGradedModuleSelfEquivTotal0 I
      (DirectSum.of (I.AssociatedGradedModulePiece R) n x) = _
  exact associatedGradedModuleSelfEquivTotal0_of I n x

/-- Let `R` be a commutative ring, `I` an ideal, `n : ℕ`, and `x ∈ I^n`. The total regular-module
equivalence sends the included module initial form of `x` to the included ring initial form of
the same representative: `E(j_n([x]_module)) = j_n([x]_ring)`. -/
theorem associatedGradedModuleSelfEquivTotal_initialFormModule
    (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    I.associatedGradedModuleSelfEquivTotal
        (DirectSum.of (I.AssociatedGradedModulePiece R) n
          (I.initialFormModule R n ⟨x, by simp [x.2]⟩)) =
      DirectSum.of I.AssociatedGradedPiece n (I.initialForm n x) := by
  rw [I.associatedGradedModuleSelfEquivTotal_of,
    I.associatedGradedModulePieceSelfEquiv_initialForm]

end Ideal
