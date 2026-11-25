/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.C0DirectSum
public import MathlibExt.Analysis.CStarAlgebra.Grading

import Mathlib.Tactic.FinCases

/-!
# Pointwise gradings of dependent coefficient C-star sums

The grading is computed on the actual CStarC0Sum carrier from the
component generators. It is not a supplied grading or a chosen model.
The generator is an actual involutive complex star-algebra equivalence;
the existing ofInvolution constructor supplies the point-norm action.

No ambient grading instance or source-specific dictionary is installed.
The coordinate maps retain their genuine nonunital star homomorphisms.
-/

@[expose] public section

noncomputable section

open scoped CStarAlgebra

namespace CStarC0Sum

universe uI uA uB

variable {I : Type uI} (A : I → Type uA)
variable [∀ i, NonUnitalCStarAlgebra (A i)]

/-- **Generator homomorphism on a graded c₀ sum.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital
complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of
norm-vanishing sections with the supremum norm. The coordinate map `(aᵢ) ↦ (σᵢ(aᵢ))` is a nonunital
complex star endomorphism of the c₀ sum. -/
def generatorHom (γ : ∀ i, CStarGrading (A i)) :
    CStarC0Sum A →⋆ₙₐ[ℂ] CStarC0Sum A :=
  map A A (fun i => NonUnitalStarAlgHom.ofClass (γ i).generatorAut)

/-- **Coordinates of the c₀ generator homomorphism.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital
complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of
norm-vanishing sections with the supremum norm. For a c₀ section `f` and `i ∈ I`, the generator
homomorphism has coordinate `σᵢ(fᵢ)`. -/
@[simp]
theorem generatorHom_apply (γ : ∀ i, CStarGrading (A i))
    (f : CStarC0Sum A) (i : I) :
    generatorHom A γ f i = (γ i).generatorAut (f i) := rfl

/-- **Involution of the c₀ generator homomorphism.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital
complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of
norm-vanishing sections with the supremum norm. Applying the coordinatewise generator homomorphism
twice returns every c₀ section. -/
theorem generatorHom_involutive (γ : ∀ i, CStarGrading (A i)) :
    Function.Involutive (generatorHom A γ) := by
  intro f
  apply ext
  intro i
  change (γ i).generatorAut ((γ i).generatorAut (f i)) = f i
  exact (γ i).generator_involutive (f i)

/-- **Star automorphism of a graded c₀ sum.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital complex
C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of norm-vanishing
sections with the supremum norm. The coordinatewise map `(aᵢ) ↦ (σᵢ(aᵢ))` is a complex star-algebra
equivalence of the sum, inverse to itself. -/
def generatorEquiv (γ : ∀ i, CStarGrading (A i)) :
    CStarC0Sum A ≃⋆ₐ[ℂ] CStarC0Sum A where
  toFun := generatorHom A γ
  invFun := generatorHom A γ
  left_inv := generatorHom_involutive A γ
  right_inv := generatorHom_involutive A γ
  map_add' := map_add (generatorHom A γ)
  map_mul' := map_mul (generatorHom A γ)
  map_star' := map_star (generatorHom A γ)
  map_smul' := map_smul (generatorHom A γ)

/-- **Coordinates of the c₀ generator equivalence.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital
complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of
norm-vanishing sections with the supremum norm. The generator equivalence has `i` coordinate
`σᵢ(fᵢ)` on every section `f`. -/
@[simp]
theorem generatorEquiv_apply (γ : ∀ i, CStarGrading (A i))
    (f : CStarC0Sum A) (i : I) :
    generatorEquiv A γ f i = (γ i).generatorAut (f i) := rfl

/-- **The c₀ generator equivalence has order two.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital
complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of
norm-vanishing sections with the supremum norm. Applying the coordinate generator equivalence twice
gives the identity on the c₀ sum. -/
theorem generatorEquiv_involutive (γ : ∀ i, CStarGrading (A i)) :
    Function.Involutive (generatorEquiv A γ) :=
  generatorHom_involutive A γ

/-- **Norm of a c₀ grading generator.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital complex
C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of norm-vanishing
sections with the supremum norm. The coordinate generator equivalence preserves the supremum norm of
each section. -/
theorem norm_generatorEquiv (γ : ∀ i, CStarGrading (A i))
    (f : CStarC0Sum A) : ‖generatorEquiv A γ f‖ = ‖f‖ :=
  StarAlgEquiv.norm_map (generatorEquiv A γ) f

/-- **Coordinatewise grading of a c₀ sum.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital complex
C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of norm-vanishing
sections with the supremum norm. The coordinatewise generators define a `ℤ/2ℤ` grading of the
completed c₀ C*-algebra, including an empty index family. -/
def grading (γ : ∀ i, CStarGrading (A i)) : CStarGrading (CStarC0Sum A) :=
  CStarGrading.ofInvolution (generatorEquiv A γ) (generatorEquiv_involutive A γ)

/-- **Generator of the coordinatewise c₀ grading.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital
complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of
norm-vanishing sections with the supremum norm. The degree-one automorphism of the c₀ grading is the
coordinate star equivalence `(aᵢ) ↦ (σᵢ(aᵢ))`. -/
@[simp]
theorem grading_generatorAut (γ : ∀ i, CStarGrading (A i)) :
    (grading A γ).generatorAut = generatorEquiv A γ :=
  CStarGrading.ofInvolution_generatorAut _ _

/-- **Coordinates of the c₀ grading action generator.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of
nonunital complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists
of norm-vanishing sections with the supremum norm. For every section `f`, its image under the
grading generator has coordinate `σᵢ(fᵢ)` at `i`. -/
@[simp]
theorem grading_generator_apply (γ : ∀ i, CStarGrading (A i))
    (f : CStarC0Sum A) (i : I) :
    (grading A γ).generatorAut f i = (γ i).generatorAut (f i) := by
  rw [grading_generatorAut]
  rfl

/-- **Every degree of the c₀ grading acts coordinatewise.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of
nonunital complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists
of norm-vanishing sections with the supremum norm. For `n ∈ ℤ/2ℤ`, the grading action sends the `i`
coordinate of a section `f` to `γᵢ(n)(fᵢ)`. -/
theorem grading_aut_apply (γ : ∀ i, CStarGrading (A i))
    (n : ZMod 2) (f : CStarC0Sum A) (i : I) :
    PointNormCStarAddAction.aut (grading A γ) n f i =
      PointNormCStarAddAction.aut (γ i) n (f i) := by
  fin_cases n
  · change (grading A γ) (0 : ZMod 2) f i = (γ i) (0 : ZMod 2) (f i)
    simp [grading]
  · rfl

/-- **Homogeneity in a c₀ sum.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital complex C*-algebras
with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of norm-vanishing sections with
the supremum norm. A c₀ section has degree `n ∈ ℤ/2ℤ` exactly when each of its coordinates has
degree `n` in its coefficient algebra. -/
theorem mem_grading_part_iff (γ : ∀ i, CStarGrading (A i))
    (n : ZMod 2) (f : CStarC0Sum A) :
    f ∈ (grading A γ).part n ↔ ∀ i, f i ∈ (γ i).part n := by
  rw [(grading A γ).mem_part_iff_generator]
  constructor
  · intro h i
    apply ((γ i).mem_part_iff_generator n (f i)).2
    have hi := congrArg (fun x : CStarC0Sum A => x i) h
    simpa only [grading_generator_apply, smul_apply] using hi
  · intro h
    apply ext
    intro i
    have hi := ((γ i).mem_part_iff_generator n (f i)).1 (h i)
    simpa only [grading_generator_apply, smul_apply] using hi

/-- **Graded evaluation from a c₀ sum.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital complex
C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of norm-vanishing
sections with the supremum norm. For each `i ∈ I`, coordinate evaluation is an equivariant nonunital
complex star homomorphism from the sum to `Aᵢ`. -/
def gradedEval (γ : ∀ i, CStarGrading (A i)) (i : I) :
    CStarGrading.Hom (grading A γ) (γ i) where
  toNonUnitalStarAlgHom := eval A i
  equivariant' := by
    intro n f
    change PointNormCStarAddAction.aut (grading A γ) n.toAdd f i =
      PointNormCStarAddAction.aut (γ i) n.toAdd (f i)
    exact grading_aut_apply A γ n.toAdd f i

/-- **Value of graded c₀ evaluation.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital complex
C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of norm-vanishing
sections with the supremum norm. The graded evaluation at coordinate `i` sends a section `f` to
`fᵢ`. -/
@[simp]
theorem gradedEval_apply (γ : ∀ i, CStarGrading (A i))
    (i : I) (f : CStarC0Sum A) : gradedEval A γ i f = f i := rfl

/-- **Underlying homomorphism of graded c₀ evaluation.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of
nonunital complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists
of norm-vanishing sections with the supremum norm. Forgetting equivariance leaves the
coordinate-evaluation nonunital star homomorphism of the c₀ sum. -/
@[simp]
theorem gradedEval_toNonUnitalStarAlgHom (γ : ∀ i, CStarGrading (A i)) (i : I) :
    (gradedEval A γ i).toNonUnitalStarAlgHom = eval A i := rfl

section Single

variable [DecidableEq I]

/-- **Graded single-coordinate inclusion.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital complex
C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of norm-vanishing
sections with the supremum norm. Assume that equality in `I` is decidable. For `i ∈ I`, placing an
element of `Aᵢ` at coordinate `i` and zero elsewhere is an equivariant nonunital star homomorphism
into the c₀ sum. -/
def gradedSingle (γ : ∀ i, CStarGrading (A i)) (i : I) :
    CStarGrading.Hom (γ i) (grading A γ) where
  toNonUnitalStarAlgHom := single A i
  equivariant' := by
    intro n a
    apply ext
    intro j
    change single A i (PointNormCStarAddAction.aut (γ i) n.toAdd a) j =
      PointNormCStarAddAction.aut (grading A γ) n.toAdd (single A i a) j
    rw [grading_aut_apply]
    by_cases hji : j = i
    · subst j
      simp
    · simp [single_apply_ne A i _ hji]

/-- **Underlying map of a graded coordinate inclusion.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of
nonunital complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists
of norm-vanishing sections with the supremum norm. Assume that equality in `I` is decidable.
Forgetting equivariance gives the single-coordinate nonunital star homomorphism from `Aᵢ` to the c₀
sum. -/
@[simp]
theorem gradedSingle_toNonUnitalStarAlgHom
    (γ : ∀ i, CStarGrading (A i)) (i : I) :
    (gradedSingle A γ i).toNonUnitalStarAlgHom = single A i := rfl

/-- **Graded evaluation retracts a matching inclusion.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of
nonunital complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists
of norm-vanishing sections with the supremum norm. Assume that equality in `I` is decidable. For `a
∈ Aᵢ`, inclusion at `i` followed by graded evaluation at `i` returns `a`. -/
@[simp]
theorem gradedEval_gradedSingle (γ : ∀ i, CStarGrading (A i))
    (i : I) (a : A i) : gradedEval A γ i (gradedSingle A γ i a) = a :=
  single_apply_self A i a

/-- **Different graded coordinates give zero.** Let `(Aᵢ)ᵢ∈I` be an arbitrary family of nonunital
complex C*-algebras with gradings `γᵢ` and generators `σᵢ`. Their c₀ direct sum consists of
norm-vanishing sections with the supremum norm. Assume that equality in `I` is decidable. For `j ≠
i`, graded evaluation at `j` of the coordinate inclusion of `a ∈ Aᵢ` is zero. -/
theorem gradedEval_gradedSingle_of_ne
    (γ : ∀ i, CStarGrading (A i)) {i j : I} (hji : j ≠ i) (a : A i) :
    gradedEval A γ j (gradedSingle A γ i a) = 0 :=
  single_apply_ne A i a hji

end Single

section FamilyMaps

variable (B : I → Type uB) [∀ i, NonUnitalCStarAlgebra (B i)]

/-- **Family map between graded c₀ sums.** Let `(Aᵢ),(Bᵢ)` be arbitrary families of graded nonunital
complex C*-algebras indexed by the same set `I`, and let `φᵢ : Aᵢ → Bᵢ` be equivariant nonunital
star homomorphisms. Both c₀ sums carry their supremum C*-norms. The coordinatewise map `(aᵢ) ↦
(φᵢ(aᵢ))` is an equivariant nonunital star homomorphism between the two coordinate-graded c₀ sums. -/
def gradedMap (γA : ∀ i, CStarGrading (A i)) (γB : ∀ i, CStarGrading (B i))
    (φ : ∀ i, CStarGrading.Hom (γA i) (γB i)) :
    CStarGrading.Hom (grading A γA) (grading B γB) where
  toNonUnitalStarAlgHom := map A B (fun i => (φ i).toNonUnitalStarAlgHom)
  equivariant' := by
    intro n f
    apply ext
    intro i
    change φ i (PointNormCStarAddAction.aut (grading A γA) n.toAdd f i) =
      PointNormCStarAddAction.aut (grading B γB) n.toAdd
        (map A B (fun j => (φ j).toNonUnitalStarAlgHom) f) i
    rw [grading_aut_apply, grading_aut_apply]
    exact CStarGrading.Hom.equivariant (φ i) n.toAdd (f i)

/-- **Coordinates of a graded c₀ family map.** Let `(Aᵢ),(Bᵢ)` be arbitrary families of graded nonunital
complex C*-algebras indexed by the same set `I`, and let `φᵢ : Aᵢ → Bᵢ` be equivariant nonunital
star homomorphisms. Both c₀ sums carry their supremum C*-norms. The `i` coordinate of the image of a
section `f` is `φᵢ(fᵢ)`. -/
@[simp]
theorem gradedMap_apply
    (γA : ∀ i, CStarGrading (A i)) (γB : ∀ i, CStarGrading (B i))
    (φ : ∀ i, CStarGrading.Hom (γA i) (γB i))
    (f : CStarC0Sum A) (i : I) :
    gradedMap A B γA γB φ f i = φ i (f i) := rfl

end FamilyMaps

end CStarC0Sum
