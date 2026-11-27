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

public import MathlibExt.Analysis.CStarAlgebra.Grading
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.Unitization
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Constructions of C-star gradings

This file supplies explicit trivial, product-swap, unitization, and finite
standard-even gradings.  It also characterizes closed graded star subalgebras.
Every grading remains a named term; importing the file installs no ambient
group action or grading instance.
-/

@[expose] public section

noncomputable section

open Set
open scoped CStarAlgebra

universe uA uB uC

namespace CStarGrading

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-! ## The trivial grading -/

/-- **Trivial C*-grading.** Let `A` be a nonunital complex C*-algebra. The action of every degree in
`ℤ/2ℤ` is the identity automorphism. -/
def trivial (A : Type uA) [NonUnitalCStarAlgebra A] : CStarGrading A :=
  PointNormCStarAction.trivial (Multiplicative (ZMod 2)) A

@[simp]
theorem trivial_apply (n : ZMod 2) (a : A) :
    PointNormCStarAddAction.aut (trivial A) n a = a :=
  rfl

@[simp]
theorem trivial_generatorAut :
    (trivial A).generatorAut = StarAlgEquiv.refl ℂ A := by
  ext a
  rfl

@[simp]
theorem trivial_evenPart : (trivial A).evenPart = ⊤ := by
  ext a
  rw [(trivial A).mem_evenPart_iff_generator]
  simp

@[simp]
theorem trivial_oddPart : (trivial A).oddPart = ⊥ := by
  ext a
  rw [(trivial A).mem_oddPart_iff_generator, Submodule.mem_bot]
  constructor
  · intro h
    have htwo : (2 : ℂ) • a = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h
    have hinv := congrArg (fun x : A ↦ (2 : ℂ)⁻¹ • x) htwo
    simpa [smul_smul] using hinv
  · rintro rfl
    simp

@[simp]
theorem trivial_evenProjection :
    (trivial A).evenProjection = ContinuousLinearMap.id ℂ A := by
  ext a
  exact (trivial A).evenProjection_eq_self_of_mem (by simp)

@[simp]
theorem trivial_oddProjection : (trivial A).oddProjection = 0 := by
  ext a
  exact (trivial A).oddProjection_eq_zero_of_mem_even (by simp)

/-! ## The swap grading on a product -/

/-- **Swap automorphism of a C*-product.** Let `A` be a nonunital complex C*-algebra. The map `(a,b) ↦
(b,a)` is an involutive complex star-algebra automorphism of `A × A`, with the product C*-norm. -/
def swapStarAlgEquiv (A : Type uA) [NonUnitalCStarAlgebra A] :
    (A × A) ≃⋆ₐ[ℂ] (A × A) where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem swapStarAlgEquiv_apply (p : A × A) :
    swapStarAlgEquiv A p = (p.2, p.1) :=
  rfl

theorem swapStarAlgEquiv_involutive :
    Function.Involutive (swapStarAlgEquiv A) :=
  fun _ ↦ rfl

/-- **Swap grading of a C*-product.** Let `A` be a nonunital complex C*-algebra. The degree-one
generator of `A × A` swaps its factors. Its even part is `{(a,a)}` and its odd part is `{(a,-a)}`. -/
def swap (A : Type uA) [NonUnitalCStarAlgebra A] :
    CStarGrading (A × A) :=
  ofInvolution (swapStarAlgEquiv A) swapStarAlgEquiv_involutive

@[simp]
theorem swap_generatorAut :
    (swap A).generatorAut = swapStarAlgEquiv A :=
  ofInvolution_generatorAut _ _

@[simp]
theorem swap_generatorAut_apply (p : A × A) :
    (swap A).generatorAut p = (p.2, p.1) :=
  rfl

theorem mem_swap_evenPart_iff (p : A × A) :
    p ∈ (swap A).evenPart ↔ p.1 = p.2 := by
  rw [(swap A).mem_evenPart_iff_generator]
  constructor
  · intro h
    exact (congrArg Prod.fst h).symm
  · intro h
    apply Prod.ext
    · exact h.symm
    · exact h

theorem mem_swap_oddPart_iff (p : A × A) :
    p ∈ (swap A).oddPart ↔ p.2 = -p.1 := by
  rw [(swap A).mem_oddPart_iff_generator]
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    apply Prod.ext
    · exact h
    · simp [h]

theorem diagonal_mem_swap_evenPart (a : A) :
    (a, a) ∈ (swap A).evenPart :=
  (mem_swap_evenPart_iff (A := A) (a, a)).2 rfl

theorem antidiagonal_mem_swap_oddPart (a : A) :
    (a, -a) ∈ (swap A).oddPart :=
  (mem_swap_oddPart_iff (A := A) (a, -a)).2 rfl

@[simp]
theorem swap_evenProjection_apply (p : A × A) :
    (swap A).evenProjection p =
      ((2 : ℂ)⁻¹ • (p.1 + p.2),
        (2 : ℂ)⁻¹ • (p.1 + p.2)) := by
  rw [evenProjection_apply]
  apply Prod.ext
  · simp
  · simp
    module

@[simp]
theorem swap_oddProjection_apply (p : A × A) :
    (swap A).oddProjection p =
      ((2 : ℂ)⁻¹ • (p.1 - p.2),
        -((2 : ℂ)⁻¹ • (p.1 - p.2))) := by
  rw [oddProjection_apply]
  apply Prod.ext
  · simp
  · simp
    module

/-! ## Products of graded algebras -/

/-- **Product of grading generators.** Let `A,B` be nonunital complex C*-algebras with `ℤ/2ℤ` gradings
`γ_A,γ_B` and generators `σ_A,σ_B`. The map `(a,b) ↦ (σ_A(a),σ_B(b))` is a complex star-algebra
automorphism of `A × B`. -/
def prodGenerator (γA : CStarGrading A) (γB : CStarGrading B) :
    (A × B) ≃⋆ₐ[ℂ] (A × B) where
  toFun p := (γA.generatorAut p.1, γB.generatorAut p.2)
  invFun p := (γA.generatorAut p.1, γB.generatorAut p.2)
  left_inv p := by
    ext
    · exact γA.generator_involutive p.1
    · exact γB.generator_involutive p.2
  right_inv p := by
    ext
    · exact γA.generator_involutive p.1
    · exact γB.generator_involutive p.2
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  map_star' _ := by
    apply Prod.ext <;> simp
  map_smul' _ _ := by simp

@[simp]
theorem prodGenerator_apply (γA : CStarGrading A)
    (γB : CStarGrading B) (p : A × B) :
    prodGenerator γA γB p =
      (γA.generatorAut p.1, γB.generatorAut p.2) :=
  rfl

theorem prodGenerator_involutive (γA : CStarGrading A)
    (γB : CStarGrading B) :
    Function.Involutive (prodGenerator γA γB) :=
  (prodGenerator γA γB).left_inv

/-- **Product grading.** Let `A,B` be nonunital complex C*-algebras with `ℤ/2ℤ` gradings `γ_A,γ_B` and
generators `σ_A,σ_B`. The coordinatewise grading on the maximum-norm C*-product `A × B` has
degree-one generator `(σ_A,σ_B)`. -/
def prod (γA : CStarGrading A) (γB : CStarGrading B) :
    CStarGrading (A × B) :=
  ofInvolution (prodGenerator γA γB)
    (prodGenerator_involutive γA γB)

@[simp]
theorem prod_generatorAut (γA : CStarGrading A)
    (γB : CStarGrading B) :
    (prod γA γB).generatorAut = prodGenerator γA γB :=
  ofInvolution_generatorAut _ _

@[simp]
theorem prod_apply (γA : CStarGrading A) (γB : CStarGrading B)
    (n : ZMod 2) (p : A × B) :
    PointNormCStarAddAction.aut (prod γA γB) n p =
      (PointNormCStarAddAction.aut γA n p.1,
        PointNormCStarAddAction.aut γB n p.2) := by
  fin_cases n
  · change (prod γA γB) (0 : ZMod 2) p =
      (γA (0 : ZMod 2) p.1, γB (0 : ZMod 2) p.2)
    simp
  · rfl

theorem mem_prod_part_iff (γA : CStarGrading A)
    (γB : CStarGrading B) (n : ZMod 2) (p : A × B) :
    p ∈ (prod γA γB).part n ↔
      p.1 ∈ γA.part n ∧ p.2 ∈ γB.part n := by
  rw [(prod γA γB).mem_part_iff_generator,
    γA.mem_part_iff_generator, γB.mem_part_iff_generator]
  constructor
  · intro h
    constructor
    · have hfst := congrArg Prod.fst h
      simpa using hfst
    · have hsnd := congrArg Prod.snd h
      simpa using hsnd
  · rintro ⟨hfst, hsnd⟩
    apply Prod.ext
    · simpa using hfst
    · simpa using hsnd

@[simp]
theorem prod_evenProjection_apply (γA : CStarGrading A)
    (γB : CStarGrading B) (p : A × B) :
    (prod γA γB).evenProjection p =
      (γA.evenProjection p.1, γB.evenProjection p.2) := by
  rw [evenProjection_apply, evenProjection_apply, evenProjection_apply]
  rfl

@[simp]
theorem prod_oddProjection_apply (γA : CStarGrading A)
    (γB : CStarGrading B) (p : A × B) :
    (prod γA γB).oddProjection p =
      (γA.oddProjection p.1, γB.oddProjection p.2) := by
  rw [oddProjection_apply, oddProjection_apply, oddProjection_apply]
  rfl

/-- **First graded product projection.** Let `A,B` be nonunital complex C*-algebras with `ℤ/2ℤ` gradings
`γ_A,γ_B` and generators `σ_A,σ_B`. The first-coordinate star homomorphism `A × B → A` is
equivariant from the product grading to `γ_A`. -/
def prodFst (γA : CStarGrading A) (γB : CStarGrading B) :
    Hom (prod γA γB) γA where
  toNonUnitalStarAlgHom := NonUnitalStarAlgHom.fst ℂ A B
  equivariant' := by
    intro n p
    change (PointNormCStarAddAction.aut (prod γA γB) n.toAdd p).1 =
      PointNormCStarAddAction.aut γA n.toAdd p.1
    rw [prod_apply]

/-- **Second graded product projection.** Let `A,B` be nonunital complex C*-algebras with `ℤ/2ℤ`
gradings `γ_A,γ_B` and generators `σ_A,σ_B`. The second-coordinate star homomorphism `A × B → B` is
equivariant from the product grading to `γ_B`. -/
def prodSnd (γA : CStarGrading A) (γB : CStarGrading B) :
    Hom (prod γA γB) γB where
  toNonUnitalStarAlgHom := NonUnitalStarAlgHom.snd ℂ A B
  equivariant' := by
    intro n p
    change (PointNormCStarAddAction.aut (prod γA γB) n.toAdd p).2 =
      PointNormCStarAddAction.aut γB n.toAdd p.2
    rw [prod_apply]

@[simp]
theorem prodFst_apply (γA : CStarGrading A)
    (γB : CStarGrading B) (p : A × B) :
    prodFst γA γB p = p.1 :=
  rfl

@[simp]
theorem prodSnd_apply (γA : CStarGrading A)
    (γB : CStarGrading B) (p : A × B) :
    prodSnd γA γB p = p.2 :=
  rfl

namespace Hom

variable [NonUnitalCStarAlgebra C]
variable {γA : CStarGrading A} {γB : CStarGrading B}
  {γC : CStarGrading C}

/-- **Pairing graded homomorphisms.** For graded nonunital complex C*-algebras `A,B,C` and equivariant
nonunital star homomorphisms `φ : C → A`, `ψ : C → B`, the map `c ↦ (φ(c),ψ(c))` is an equivariant
nonunital star homomorphism from `C` to the product-graded C*-algebra `A × B`. -/
def prod (φ : Hom γC γA) (ψ : Hom γC γB) :
    Hom γC (CStarGrading.prod γA γB) where
  toNonUnitalStarAlgHom :=
    NonUnitalStarAlgHom.prod φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom
  equivariant' := by
    intro n c
    change (φ (PointNormCStarAddAction.aut γC n.toAdd c),
        ψ (PointNormCStarAddAction.aut γC n.toAdd c)) =
      PointNormCStarAddAction.aut (CStarGrading.prod γA γB)
        n.toAdd (φ c, ψ c)
    rw [CStarGrading.prod_apply, φ.equivariant, ψ.equivariant]

@[simp]
theorem prod_apply (φ : Hom γC γA) (ψ : Hom γC γB) (c : C) :
    prod φ ψ c = (φ c, ψ c) :=
  rfl

end Hom

/-! ## Unitization -/

/-- **Grading of the complex unitization.** Let `A` be a nonunital complex C*-algebra with a `ℤ/2ℤ`
grading `γ`. The action extends to the complex unitization by `γ̃(s)(λ,a) = (λ,γ(s)a)`, fixing the
scalar coordinate. -/
def unitization (γ : CStarGrading A) :
    CStarGrading (Unitization ℂ A) :=
  PointNormCStarAction.unitizationAction γ

@[simp]
theorem unitization_apply (γ : CStarGrading A) (n : ZMod 2)
    (x : Unitization ℂ A) :
    PointNormCStarAddAction.aut γ.unitization n x =
      Unitization.inl x.fst +
        Unitization.inr (PointNormCStarAddAction.aut γ n x.snd) :=
  PointNormCStarAction.unitizationAction_apply γ
    (Multiplicative.ofAdd n) x

@[simp]
theorem unitization_generatorAut_apply (γ : CStarGrading A)
    (x : Unitization ℂ A) :
    γ.unitization.generatorAut x =
      Unitization.inl x.fst + Unitization.inr (γ.generatorAut x.snd) := by
  exact γ.unitization_apply 1 x

theorem unitization_inl_mem_evenPart (γ : CStarGrading A) (z : ℂ) :
    Unitization.inl z ∈ γ.unitization.evenPart := by
  rw [γ.unitization.mem_evenPart_iff_generator]
  rw [unitization_generatorAut_apply]
  simp

theorem unitization_mem_evenPart_iff (γ : CStarGrading A)
    (x : Unitization ℂ A) :
    x ∈ γ.unitization.evenPart ↔ x.snd ∈ γ.evenPart := by
  rw [γ.unitization.mem_evenPart_iff_generator,
    γ.mem_evenPart_iff_generator]
  constructor
  · intro h
    rw [unitization_generatorAut_apply] at h
    have hsnd := congrArg (fun y : Unitization ℂ A ↦ y.snd) h
    simpa using hsnd
  · intro h
    rw [unitization_generatorAut_apply, h]
    exact Unitization.inl_fst_add_inr_snd_eq x

theorem unitization_mem_oddPart_iff (γ : CStarGrading A)
    (x : Unitization ℂ A) :
    x ∈ γ.unitization.oddPart ↔
      x.fst = 0 ∧ x.snd ∈ γ.oddPart := by
  rw [γ.unitization.mem_oddPart_iff_generator,
    γ.mem_oddPart_iff_generator]
  constructor
  · intro h
    rw [unitization_generatorAut_apply] at h
    have hfst := congrArg (fun y : Unitization ℂ A ↦ y.fst) h
    have hsnd := congrArg (fun y : Unitization ℂ A ↦ y.snd) h
    constructor
    · have hfst' : x.fst = -x.fst := by
        simpa only [Unitization.fst_add, Unitization.fst_inl,
          Unitization.fst_inr, add_zero, Unitization.fst_neg] using hfst
      exact CharZero.eq_neg_self_iff.mp hfst'
    · simpa only [Unitization.snd_add, Unitization.snd_inl,
        Unitization.snd_inr, zero_add, Unitization.snd_neg] using hsnd
  · rintro ⟨hfst, hsnd⟩
    rw [unitization_generatorAut_apply, hsnd]
    apply Unitization.ext
    · simp [hfst]
    · simp

theorem unitization_inr_mem_part_iff (γ : CStarGrading A)
    (n : ZMod 2) (a : A) :
    Unitization.inr a ∈ γ.unitization.part n ↔ a ∈ γ.part n := by
  rw [γ.unitization.mem_part_iff_generator, γ.mem_part_iff_generator]
  constructor
  · intro h
    rw [unitization_generatorAut_apply] at h
    have hsnd := congrArg (fun x : Unitization ℂ A ↦ x.snd) h
    simpa using hsnd
  · intro h
    rw [unitization_generatorAut_apply]
    simp [h]

/-- **Graded inclusion into the unitization.** Let `A` be a nonunital complex C*-algebra with a `ℤ/2ℤ`
grading `γ`. The coefficient inclusion `a ↦ (0,a)` is an equivariant nonunital complex star
homomorphism into the induced grading on the complex unitization. -/
def unitizationInclusion (γ : CStarGrading A) :
    Hom γ γ.unitization :=
  PointNormCStarAction.unitizationInclusion γ

@[simp]
theorem unitizationInclusion_apply (γ : CStarGrading A) (a : A) :
    γ.unitizationInclusion a = Unitization.inr a :=
  rfl

/-! ## Graded closed star subalgebras -/

/-- **Invariance of a star subalgebra under grading.** Let `A` be a nonunital complex C*-algebra with a
`ℤ/2ℤ` grading `γ`. A nonunital star subalgebra `S ⊆ A` is graded when the degree-one generator
sends every element of `S` into `S`; this invariance condition alone does not require closedness. -/
def IsGradedSubalgebra (γ : CStarGrading A)
    (S : NonUnitalStarSubalgebra ℂ A) : Prop :=
  IsClosed (S : Set A) ∧
    ∀ a : A, a ∈ S → γ.generatorAut a ∈ S

theorem IsGradedSubalgebra.isClosed {γ : CStarGrading A}
    {S : NonUnitalStarSubalgebra ℂ A}
    (hS : IsGradedSubalgebra γ S) :
    IsClosed (S : Set A) :=
  hS.1

theorem IsGradedSubalgebra.generator_mem {γ : CStarGrading A}
    {S : NonUnitalStarSubalgebra ℂ A}
    (hS : IsGradedSubalgebra γ S) {a : A} (ha : a ∈ S) :
    γ.generatorAut a ∈ S :=
  hS.2 a ha

theorem generator_eq_evenProjection_sub_oddProjection
    (γ : CStarGrading A) (a : A) :
    γ.generatorAut a = γ.evenProjection a - γ.oddProjection a := by
  rw [evenProjection_apply, oddProjection_apply]
  module

theorem isGradedSubalgebra_iff_projections
    (γ : CStarGrading A) (S : NonUnitalStarSubalgebra ℂ A) :
    IsGradedSubalgebra γ S ↔
      IsClosed (S : Set A) ∧
        ∀ a : A, a ∈ S →
          γ.evenProjection a ∈ S ∧ γ.oddProjection a ∈ S := by
  constructor
  · rintro ⟨hclosed, hinv⟩
    refine ⟨hclosed, ?_⟩
    intro a ha
    constructor
    · rw [evenProjection_apply]
      exact S.smul_mem _ (S.add_mem ha (hinv a ha))
    · rw [oddProjection_apply]
      exact S.smul_mem _ (S.sub_mem ha (hinv a ha))
  · rintro ⟨hclosed, hparts⟩
    refine ⟨hclosed, ?_⟩
    intro a ha
    rw [γ.generator_eq_evenProjection_sub_oddProjection]
    exact S.sub_mem (hparts a ha).1 (hparts a ha).2

theorem IsGradedSubalgebra.evenProjection_mem
    {γ : CStarGrading A} {S : NonUnitalStarSubalgebra ℂ A}
    (hS : IsGradedSubalgebra γ S) {a : A} (ha : a ∈ S) :
    γ.evenProjection a ∈ S :=
  ((γ.isGradedSubalgebra_iff_projections S).1 hS).2 a ha |>.1

theorem IsGradedSubalgebra.oddProjection_mem
    {γ : CStarGrading A} {S : NonUnitalStarSubalgebra ℂ A}
    (hS : IsGradedSubalgebra γ S) {a : A} (ha : a ∈ S) :
    γ.oddProjection a ∈ S :=
  ((γ.isGradedSubalgebra_iff_projections S).1 hS).2 a ha |>.2

/-! ## Restriction to a closed invariant star subalgebra -/

section RestrictSubalgebra

variable (γ : CStarGrading A) (S : NonUnitalStarSubalgebra ℂ A)
variable [hSclosed : IsClosed (S : Set A)]
variable (hSinv : ∀ a : A, a ∈ S → γ.generatorAut a ∈ S)

/-- **Restricted grading generator.** Let `A` be a nonunital complex C*-algebra with grading `γ` and
generator `σ`, and let `S ⊆ A` be a norm-closed nonunital star subalgebra invariant under `σ`. The
generator restricts to the complex star-algebra automorphism `σ|S : S ≃ S`. -/
def restrictGenerator : S ≃⋆ₐ[ℂ] S where
  toFun a := ⟨γ.generatorAut a, hSinv a a.property⟩
  invFun a := ⟨γ.generatorAut a, hSinv a a.property⟩
  left_inv a := by
    apply Subtype.ext
    exact γ.generator_involutive a
  right_inv a := by
    apply Subtype.ext
    exact γ.generator_involutive a
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add γ.generatorAut _ _
  map_mul' _ _ := by
    apply Subtype.ext
    exact map_mul γ.generatorAut _ _
  map_star' _ := by
    apply Subtype.ext
    exact map_star γ.generatorAut _
  map_smul' _ _ := by
    apply Subtype.ext
    exact map_smul γ.generatorAut _ _

omit hSclosed in
@[simp]
theorem restrictGenerator_apply (a : S) :
    ((restrictGenerator γ S hSinv a : S) : A) = γ.generatorAut a :=
  rfl

omit hSclosed in
theorem restrictGenerator_involutive :
    Function.Involutive (restrictGenerator γ S hSinv) :=
  (restrictGenerator γ S hSinv).left_inv

/-- **Grading of a closed invariant star subalgebra.** Let `A` be a nonunital complex C*-algebra with
grading `γ` and generator `σ`, and let `S ⊆ A` be a norm-closed nonunital star subalgebra invariant
under `σ`. Restricting the grading generator gives a `ℤ/2ℤ` grading on `S`, with its inherited
C*-norm. -/
def restrictSubalgebra : CStarGrading S :=
  ofInvolution (restrictGenerator γ S hSinv)
    (restrictGenerator_involutive γ S hSinv)

@[simp]
theorem restrictSubalgebra_generatorAut :
    (restrictSubalgebra γ S hSinv).generatorAut =
      restrictGenerator γ S hSinv :=
  ofInvolution_generatorAut _ _

theorem mem_restrictSubalgebra_part_iff (n : ZMod 2) (a : S) :
    a ∈ (restrictSubalgebra γ S hSinv).part n ↔
      (a : A) ∈ γ.part n := by
  rw [(restrictSubalgebra γ S hSinv).mem_part_iff_generator,
    γ.mem_part_iff_generator]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

@[simp]
theorem restrictSubalgebra_evenProjection_apply (a : S) :
    (((restrictSubalgebra γ S hSinv).evenProjection a : S) : A) =
      γ.evenProjection a := by
  rw [evenProjection_apply, evenProjection_apply]
  rfl

@[simp]
theorem restrictSubalgebra_oddProjection_apply (a : S) :
    (((restrictSubalgebra γ S hSinv).oddProjection a : S) : A) =
      γ.oddProjection a := by
  rw [oddProjection_apply, oddProjection_apply]
  rfl

/-- **Equivariant inclusion of a restricted grading.** Let `A` be a nonunital complex C*-algebra with
grading `γ` and generator `σ`, and let `S ⊆ A` be a norm-closed nonunital star subalgebra invariant
under `σ`. The inclusion `S ↪ A` is an equivariant nonunital complex star homomorphism from the
restricted grading to `γ`. -/
def restrictSubalgebraInclusion :
    Hom (restrictSubalgebra γ S hSinv) γ where
  toNonUnitalStarAlgHom := NonUnitalStarSubalgebraClass.subtype S
  equivariant' := by
    intro n a
    fin_cases n
    · change
        (((PointNormCStarAddAction.aut
          (restrictSubalgebra γ S hSinv) 0) a : S) : A) =
          PointNormCStarAddAction.aut γ 0 (a : A)
      simp
    · change
        (((restrictSubalgebra γ S hSinv).generatorAut a : S) : A) =
          γ.generatorAut (a : A)
      rfl

@[simp]
theorem restrictSubalgebraInclusion_apply (a : S) :
    restrictSubalgebraInclusion γ S hSinv a = (a : A) :=
  rfl

end RestrictSubalgebra

/-! ## The standard-even grading on two-by-two matrices -/

section StandardEvenMatrix

local instance coefficientSpectralOrder : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance coefficientSpectralOrderedRing : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- **Signs for the standard two-by-two grading.** The row and column sign on `Fin 2` is `1` at index
zero and `-1` at index one. -/
def standardEvenIndexSign (i : Fin 2) : ℂ :=
  if i = 0 then 1 else -1

@[simp]
theorem standardEvenIndexSign_zero : standardEvenIndexSign 0 = 1 := by
  simp [standardEvenIndexSign]

@[simp]
theorem standardEvenIndexSign_one : standardEvenIndexSign 1 = -1 := by
  simp [standardEvenIndexSign]

@[simp]
theorem standardEvenIndexSign_sq (i : Fin 2) :
    standardEvenIndexSign i * standardEvenIndexSign i = 1 := by
  fin_cases i <;> norm_num

def standardEvenMatrixMap
    (M : CStarMatrix (Fin 2) (Fin 2) A) :
    CStarMatrix (Fin 2) (Fin 2) A :=
  fun i j ↦
    (standardEvenIndexSign i * standardEvenIndexSign j) • M i j

@[simp]
theorem standardEvenMatrixMap_apply
    (M : CStarMatrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    standardEvenMatrixMap M i j =
      (standardEvenIndexSign i * standardEvenIndexSign j) • M i j :=
  rfl

/-- **Generator of the standard even matrix grading.** Let `A` be a nonunital complex C*-algebra. The
two-by-two C*-matrix algebra over `A` has an involutive star automorphism fixing diagonal entries
and negating off-diagonal entries. -/
def standardEvenMatrixGenerator :
    CStarMatrix (Fin 2) (Fin 2) A ≃⋆ₐ[ℂ]
      CStarMatrix (Fin 2) (Fin 2) A where
  toFun := standardEvenMatrixMap
  invFun := standardEvenMatrixMap
  left_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardEvenMatrixMap]
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardEvenMatrixMap]
  map_add' M N := by
    ext i j
    simp [standardEvenMatrixMap, smul_add]
  map_mul' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardEvenMatrixMap, CStarMatrix.mul_apply,
        Fin.sum_univ_two] <;>
      abel
  map_star' M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardEvenMatrixMap, CStarMatrix.star_apply]
  map_smul' z M := by
    ext i j
    simp [standardEvenMatrixMap, smul_smul, mul_comm]

@[simp]
theorem standardEvenMatrixGenerator_apply
    (M : CStarMatrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    standardEvenMatrixGenerator M i j =
      (standardEvenIndexSign i * standardEvenIndexSign j) • M i j :=
  standardEvenMatrixMap_apply M i j

theorem standardEvenMatrixGenerator_involutive :
    Function.Involutive
      (standardEvenMatrixGenerator (A := A)) :=
  (standardEvenMatrixGenerator (A := A)).left_inv

/-- **Standard even grading on two-by-two matrices.** Let `A` be a nonunital complex C*-algebra. The
generator fixes diagonal entries and negates off-diagonal entries, making diagonal matrices even and
off-diagonal matrices odd. -/
def standardEvenMatrix :
    CStarGrading (CStarMatrix (Fin 2) (Fin 2) A) :=
  ofInvolution standardEvenMatrixGenerator
    standardEvenMatrixGenerator_involutive

@[simp]
theorem standardEvenMatrix_generatorAut :
    (standardEvenMatrix (A := A)).generatorAut =
      standardEvenMatrixGenerator :=
  ofInvolution_generatorAut _ _

theorem mem_standardEvenMatrix_evenPart_iff
    (M : CStarMatrix (Fin 2) (Fin 2) A) :
    M ∈ (standardEvenMatrix (A := A)).evenPart ↔
      M 0 1 = 0 ∧ M 1 0 = 0 := by
  rw [(standardEvenMatrix (A := A)).mem_evenPart_iff_generator]
  constructor
  · intro h
    have h01 := congrArg (fun N : CStarMatrix (Fin 2) (Fin 2) A ↦ N 0 1) h
    have h10 := congrArg (fun N : CStarMatrix (Fin 2) (Fin 2) A ↦ N 1 0) h
    constructor
    · have h01' : -M 0 1 = M 0 1 := by simpa using h01
      apply (smul_eq_zero.mp ?_).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h01'.symm
    · have h10' : -M 1 0 = M 1 0 := by simpa using h10
      apply (smul_eq_zero.mp ?_).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h10'.symm
  · rintro ⟨h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h01, h10]

theorem mem_standardEvenMatrix_oddPart_iff
    (M : CStarMatrix (Fin 2) (Fin 2) A) :
    M ∈ (standardEvenMatrix (A := A)).oddPart ↔
      M 0 0 = 0 ∧ M 1 1 = 0 := by
  rw [(standardEvenMatrix (A := A)).mem_oddPart_iff_generator]
  constructor
  · intro h
    have h00 := congrArg (fun N : CStarMatrix (Fin 2) (Fin 2) A ↦ N 0 0) h
    have h11 := congrArg (fun N : CStarMatrix (Fin 2) (Fin 2) A ↦ N 1 1) h
    constructor
    · have h00' : M 0 0 = -M 0 0 := by simpa using h00
      apply (smul_eq_zero.mp ?_).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h00'
    · have h11' : M 1 1 = -M 1 1 := by simpa using h11
      apply (smul_eq_zero.mp ?_).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h11'
  · rintro ⟨h00, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h00, h11]

end StandardEvenMatrix

end CStarGrading
