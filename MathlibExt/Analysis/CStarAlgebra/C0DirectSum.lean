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

public import Mathlib.Analysis.CStarAlgebra.lpSpace
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import Mathlib.Topology.Algebra.Module.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dependent coefficient C-star direct sums

The carrier is the literal vanishing-norm subalgebra of the dependent
bounded product lp A ∞. Its norm, complex action, star and completeness
come from Mathlib's ambient C-star algebra and closed-subalgebra API.
There is no countability or separability assumption on the constructor.

Finite coordinate cutoffs give approximation in the supremum norm.
Countability and separability enter only the derived separability
instance. Coordinate maps are nonunital complex star homomorphisms.
-/

@[expose] public section

noncomputable section

open Set
open TopologicalSpace
open scoped ENNReal BigOperators Topology CStarAlgebra

namespace CStarC0Sum

universe uI uA uB uC

section Vanishing

variable {I : Type uI} {E : I → Type uA}
variable [∀ i, NormedAddCommGroup (E i)]

/-- **Norm vanishing along the cofinite filter.** For an arbitrary family `(Eᵢ)ᵢ∈I` of normed additive
commutative groups, a section `fᵢ ∈ Eᵢ` vanishes at the cofinite filter when `{i : ‖fᵢ‖ ≥ ε}` is
finite for every `ε > 0`. This condition is the definition of `VanishesAtCofinite`. -/
def VanishesAtCofinite (f : ∀ i, E i) : Prop :=
  ∀ ε : ℝ, 0 < ε → Set.Finite {i : I | ε ≤ ‖f i‖}

/-- **Zero section vanishes at cofinite.** For an arbitrary family `(Eᵢ)ᵢ∈I` of normed additive
commutative groups, a section `fᵢ ∈ Eᵢ` vanishes at the cofinite filter when `{i : ‖fᵢ‖ ≥ ε}` is
finite for every `ε > 0`. The zero section satisfies this condition, including when `I` is empty. -/
theorem vanishes_zero : VanishesAtCofinite (fun i : I => (0 : E i)) := by
  intro ε hε
  have hempty : {i : I | ε ≤ ‖(0 : E i)‖} = ∅ := by
    ext i
    simp [not_le_of_gt hε]
  rw [hempty]
  exact Set.finite_empty

/-- **Finite support implies norm vanishing.** For an arbitrary family `(Eᵢ)ᵢ∈I` of normed additive
commutative groups, a section `fᵢ ∈ Eᵢ` vanishes at the cofinite filter when `{i : ‖fᵢ‖ ≥ ε}` is
finite for every `ε > 0`. If the set `{i : fᵢ ≠ 0}` is finite, the section satisfies this condition. -/
theorem vanishes_of_finite_support {f : ∀ i, E i}
    (hf : Set.Finite {i : I | f i ≠ 0}) : VanishesAtCofinite f := by
  intro ε hε
  refine hf.subset fun i hi => ?_
  intro hzero
  exact (not_le_of_gt hε) (by simpa [hzero] using hi)

/-- **Norm-vanishing sections are bounded.** For an arbitrary family `(Eᵢ)ᵢ∈I` of normed additive
commutative groups, a section `fᵢ ∈ Eᵢ` vanishes at the cofinite filter when `{i : ‖fᵢ‖ ≥ ε}` is
finite for every `ε > 0`. If `f` vanishes at cofinite, the set of coordinate norms `{‖fᵢ‖ : i ∈ I}`
is bounded above in `ℝ`. -/
theorem VanishesAtCofinite.bddAbove_range_norm {f : ∀ i, E i}
    (hf : VanishesAtCofinite f) : BddAbove (Set.range fun i => ‖f i‖) := by
  obtain ⟨C, hC⟩ := ((hf 1 zero_lt_one).image fun i => ‖f i‖).bddAbove
  refine ⟨max 1 C, ?_⟩
  rintro _ ⟨i, rfl⟩
  by_cases hi : 1 ≤ ‖f i‖
  · exact (hC ⟨i, hi, rfl⟩).trans (le_max_right _ _)
  · exact (le_of_lt (lt_of_not_ge hi)).trans (le_max_left _ _)

/-- **Norm-vanishing sections belong to ℓ∞.** For an arbitrary family `(Eᵢ)ᵢ∈I` of normed additive
commutative groups, a section `fᵢ ∈ Eᵢ` vanishes at the cofinite filter when `{i : ‖fᵢ‖ ≥ ε}` is
finite for every `ε > 0`. A section vanishing at cofinite has bounded coordinate norms and belongs
to the bounded product `ℓ∞(Eᵢ)`. -/
theorem VanishesAtCofinite.mem_lp_infty {f : ∀ i, E i}
    (hf : VanishesAtCofinite f) : Memℓp f ∞ :=
  memℓp_infty hf.bddAbove_range_norm

/-- **Addition preserves norm vanishing.** For an arbitrary family `(Eᵢ)ᵢ∈I` of normed additive
commutative groups, a section `fᵢ ∈ Eᵢ` vanishes at the cofinite filter when `{i : ‖fᵢ‖ ≥ ε}` is
finite for every `ε > 0`. If `f` and `g` both vanish at cofinite, the section `(fᵢ + gᵢ)ᵢ` does too. -/
theorem VanishesAtCofinite.add {f g : ∀ i, E i}
    (hf : VanishesAtCofinite f) (hg : VanishesAtCofinite g) :
    VanishesAtCofinite (fun i => f i + g i) := by
  intro ε hε
  refine ((hf (ε / 2) (half_pos hε)).union
    (hg (ε / 2) (half_pos hε))).subset fun i hi => ?_
  change ε ≤ ‖f i + g i‖ at hi
  by_cases hfi : ε / 2 ≤ ‖f i‖
  · exact Or.inl hfi
  · right
    by_contra hgi
    change ¬ ε / 2 ≤ ‖g i‖ at hgi
    have hadd := norm_add_le (f i) (g i)
    have hfl := lt_of_not_ge hfi
    have hgl := lt_of_not_ge hgi
    linarith

/-- **Negation preserves norm vanishing.** For an arbitrary family `(Eᵢ)ᵢ∈I` of normed additive
commutative groups, a section `fᵢ ∈ Eᵢ` vanishes at the cofinite filter when `{i : ‖fᵢ‖ ≥ ε}` is
finite for every `ε > 0`. If `f` vanishes at cofinite, the section `(-fᵢ)ᵢ` does too. -/
theorem VanishesAtCofinite.neg {f : ∀ i, E i}
    (hf : VanishesAtCofinite f) :
    VanishesAtCofinite (fun i => -f i) := by
  intro ε hε
  simpa only [norm_neg] using hf ε hε

/-- **Subtraction preserves norm vanishing.** For an arbitrary family `(Eᵢ)ᵢ∈I` of normed additive
commutative groups, a section `fᵢ ∈ Eᵢ` vanishes at the cofinite filter when `{i : ‖fᵢ‖ ≥ ε}` is
finite for every `ε > 0`. If `f` and `g` both vanish at cofinite, the section `(fᵢ - gᵢ)ᵢ` does too. -/
theorem VanishesAtCofinite.sub {f g : ∀ i, E i}
    (hf : VanishesAtCofinite f) (hg : VanishesAtCofinite g) :
    VanishesAtCofinite (fun i => f i - g i) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

variable {F : I → Type uB} [∀ i, NormedAddCommGroup (F i)]

/-- **Norm domination preserves cofinite vanishing.** Let `(Eᵢ)` and `(Fᵢ)` be families of normed
additive commutative groups indexed by the same arbitrary set `I`. If `fᵢ ∈ Eᵢ` vanishes at
cofinite, `K > 0`, and `‖gᵢ‖ ≤ K ‖fᵢ‖` for every `i`, then `gᵢ ∈ Fᵢ` also vanishes at cofinite. -/
theorem VanishesAtCofinite.of_norm_le_const_mul {f : ∀ i, E i}
    (hf : VanishesAtCofinite f) {g : ∀ i, F i}
    {K : ℝ} (hK : 0 < K) (hfg : ∀ i, ‖g i‖ ≤ K * ‖f i‖) :
    VanishesAtCofinite g := by
  intro ε hε
  refine (hf (ε / K) (div_pos hε hK)).subset fun i hi => ?_
  apply (div_le_iff₀ hK).2
  simpa only [mul_comm] using hi.trans (hfg i)

/-- **Equal coordinate norms preserve cofinite vanishing.** For two families of normed additive
commutative groups indexed by the same set `I`, if sections `f,g` satisfy `‖gᵢ‖ = ‖fᵢ‖` for every
`i` and `f` vanishes at cofinite, then `g` does too. -/
theorem VanishesAtCofinite.of_norm_eq {f : ∀ i, E i}
    (hf : VanishesAtCofinite f) {g : ∀ i, F i}
    (hfg : ∀ i, ‖g i‖ = ‖f i‖) : VanishesAtCofinite g := by
  intro ε hε
  simpa only [hfg] using hf ε hε

end Vanishing

section Closedness

variable {I : Type uI} (E : I → Type uA)
variable [∀ i, NormedAddCommGroup (E i)]

/-- **Closedness of norm-vanishing sections.** For any family `(Eᵢ)ᵢ∈I` of normed additive commutative
groups, the sections vanishing at the cofinite filter form a closed subset of the bounded product
`ℓ∞(Eᵢ)` in the supremum-norm topology. Completeness of the fibers is not assumed. -/
theorem isClosed_vanishing :
    IsClosed {f : lp E ∞ | VanishesAtCofinite (fun i => f i)} := by
  apply isClosed_of_closure_subset
  intro f hf ε hε
  obtain ⟨g, hg, hfg⟩ :=
    Metric.mem_closure_iff.mp hf (ε / 2) (half_pos hε)
  refine (hg (ε / 2) (half_pos hε)).subset fun i hi => ?_
  change ε ≤ ‖f i‖ at hi
  change ε / 2 ≤ ‖g i‖
  have hdist : ‖f - g‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hfg
  have hcoord : ‖f i - g i‖ ≤ ‖f - g‖ :=
    lp.norm_apply_le_norm (by simp) (f - g) i
  have htriangle : ‖f i‖ ≤ ‖f i - g i‖ + ‖g i‖ := by
    calc
      ‖f i‖ = ‖(f i - g i) + g i‖ := by rw [sub_add_cancel]
      _ ≤ ‖f i - g i‖ + ‖g i‖ := norm_add_le _ _
  linarith

end Closedness

section Subalgebra

variable {I : Type uI} (A : I → Type uA)
variable [∀ i, NonUnitalCStarAlgebra (A i)]

/-- **c₀ sum as a star subalgebra.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras,
its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations and the
supremum norm. It is the nonunital complex star subalgebra of the bounded product `ℓ∞(Aᵢ)` whose
sections vanish at cofinite. -/
def subalgebra : NonUnitalStarSubalgebra ℂ (lp A ∞) where
  carrier := {f | VanishesAtCofinite (fun i => f i)}
  zero_mem' := vanishes_zero
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    apply hg.of_norm_le_const_mul (K := ‖f‖ + 1) (by positivity)
    intro i
    calc
      ‖f i * g i‖ ≤ ‖f i‖ * ‖g i‖ := norm_mul_le _ _
      _ ≤ (‖f‖ + 1) * ‖g i‖ := mul_le_mul_of_nonneg_right
        ((lp.norm_apply_le_norm (by simp) f i).trans (by linarith)) (norm_nonneg _)
  smul_mem' := by
    intro c f hf
    apply hf.of_norm_le_const_mul (K := ‖c‖ + 1) (by positivity)
    intro i
    calc
      ‖c • f i‖ ≤ ‖c‖ * ‖f i‖ := norm_smul_le _ _
      _ ≤ (‖c‖ + 1) * ‖f i‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  star_mem' := by
    intro f hf
    exact hf.of_norm_eq (fun i => norm_star (f i))

/-- **Membership in the c₀ subalgebra.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. A bounded section belongs to this subalgebra exactly when each positive norm
level set `{i : ‖aᵢ‖ ≥ ε}` is finite. -/
@[simp]
theorem mem_subalgebra (f : lp A ∞) :
    f ∈ subalgebra A ↔ VanishesAtCofinite (fun i => f i) :=
  Iff.rfl

/-- **Closedness of the c₀ star subalgebra.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. The c₀ subalgebra is closed in the supremum-norm topology of `ℓ∞(Aᵢ)`. -/
theorem isClosed_subalgebra : IsClosed (subalgebra A : Set (lp A ∞)) :=
  isClosed_vanishing A

end Subalgebra

end CStarC0Sum

universe uC0Index uC0Fiber

/-- **Heterogeneous c₀ C*-direct sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. This is the complete nonunital complex C*-algebra on that carrier, including
the zero algebra when `I` is empty. -/
@[reducible]
noncomputable def CStarC0Sum {I : Type uC0Index} (A : I → Type uC0Fiber)
    [∀ i, NonUnitalCStarAlgebra (A i)] : Type (max uC0Index uC0Fiber) :=
  ↥(CStarC0Sum.subalgebra A)

namespace CStarC0Sum

universe uI uA uB uC

variable {I : Type uI} (A : I → Type uA)
variable [∀ i, NonUnitalCStarAlgebra (A i)]

/-- All eight dictionaries are the stock closed-subalgebra dictionaries. -/
noncomputable instance instNonUnitalCStarAlgebra :
    NonUnitalCStarAlgebra (CStarC0Sum A) := by
  letI : IsClosed (subalgebra A : Set (lp A ∞)) := isClosed_subalgebra A
  exact inferInstanceAs (NonUnitalCStarAlgebra ↥(subalgebra A))

/-- Evaluation notation for a dependent coefficient family. -/
instance instCoeFun : CoeFun (CStarC0Sum A) (fun _ => ∀ i, A i) :=
  ⟨fun f i => f.1 i⟩

/-- **Inclusion of a c₀ sum into ℓ∞.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. The inclusion into `ℓ∞(Aᵢ)` retains every coordinate of the section. -/
def toLp (f : CStarC0Sum A) : lp A ∞ := f.1

/-- **Coordinates of the inclusion into ℓ∞.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. For a c₀ section `f`, its included bounded section has coordinate `fᵢ` at
every `i`. -/
@[simp]
theorem toLp_apply (f : CStarC0Sum A) (i : I) : toLp A f i = f i := rfl

/-- **Vanishing property of c₀ sections.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. For every c₀ section `f` and `ε > 0`, the set `{i : ‖fᵢ‖ ≥ ε}` is finite. -/
theorem vanishes (f : CStarC0Sum A) :
    VanishesAtCofinite (fun i => f i) := f.2

/-- **Constructing a c₀ section.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras,
its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations and the
supremum norm. Any section `fᵢ ∈ Aᵢ` satisfying the cofinite norm-vanishing condition determines an
element of the c₀ direct sum; its boundedness follows from vanishing. -/
def ofFunction (f : ∀ i, A i) (hf : VanishesAtCofinite f) : CStarC0Sum A :=
  ⟨⟨f, hf.mem_lp_infty⟩, hf⟩

/-- **Coordinates of a constructed c₀ section.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. For a section `f` vanishing at cofinite, its element in the c₀ direct sum has
coordinate `fᵢ` at every `i`. -/
@[simp]
theorem ofFunction_apply (f : ∀ i, A i) (hf : VanishesAtCofinite f) (i : I) :
    ofFunction A f hf i = f i := rfl

/-- **Extensionality of c₀ sections.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Two elements of the c₀ sum are equal when all their coordinates agree. -/
@[ext]
theorem ext {f g : CStarC0Sum A} (h : ∀ i, f i = g i) : f = g := by
  apply Subtype.ext
  apply lp.ext
  exact funext h

/-- **Zero in a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras, its c₀
direct sum consists of norm-vanishing sections with coordinatewise operations and the supremum norm.
The zero element has zero in every coordinate. -/
@[simp]
theorem zero_apply (i : I) : (0 : CStarC0Sum A) i = 0 := rfl

/-- **Addition in a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras, its c₀
direct sum consists of norm-vanishing sections with coordinatewise operations and the supremum norm.
For sections `f,g`, the `i` coordinate of `f + g` is `fᵢ + gᵢ`. -/
@[simp]
theorem add_apply (f g : CStarC0Sum A) (i : I) : (f + g) i = f i + g i := rfl

/-- **Multiplication in a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras,
its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations and the
supremum norm. For sections `f,g`, the `i` coordinate of `f g` is `fᵢ gᵢ`. -/
@[simp]
theorem mul_apply (f g : CStarC0Sum A) (i : I) : (f * g) i = f i * g i := rfl

/-- **Involution in a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras, its
c₀ direct sum consists of norm-vanishing sections with coordinatewise operations and the supremum
norm. For a section `f`, the `i` coordinate of `f*` is `(fᵢ)*`. -/
@[simp]
theorem star_apply (f : CStarC0Sum A) (i : I) : star f i = star (f i) := rfl

/-- **Complex scalar multiplication in a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital
complex C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise
operations and the supremum norm. For `c ∈ ℂ` and a section `f`, the `i` coordinate of `c f` is `c
fᵢ`. -/
@[simp]
theorem smul_apply (c : ℂ) (f : CStarC0Sum A) (i : I) : (c • f) i = c • f i := rfl

/-- **Subtraction in a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras, its
c₀ direct sum consists of norm-vanishing sections with coordinatewise operations and the supremum
norm. For sections `f,g`, the `i` coordinate of `f - g` is `fᵢ - gᵢ`. -/
@[simp]
theorem sub_apply (f g : CStarC0Sum A) (i : I) : (f - g) i = f i - g i := rfl

/-- **Isometric inclusion of c₀ into ℓ∞.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. For every c₀ section `f`, its norm in the bounded product equals its norm in
the c₀ sum. -/
@[simp]
theorem norm_toLp (f : CStarC0Sum A) : ‖toLp A f‖ = ‖f‖ := rfl

/-- **Supremum norm of a c₀ section.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. For a section `f`, `‖f‖ = supᵢ ‖fᵢ‖`, with value zero for the empty family. -/
theorem norm_eq_ciSup (f : CStarC0Sum A) : ‖f‖ = ⨆ i, ‖f i‖ :=
  lp.norm_eq_ciSup (toLp A f)

/-- **Coordinate norm bound in a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. For every section `f` and coordinate `i`, `‖fᵢ‖ ≤ ‖f‖`. -/
theorem norm_apply_le (f : CStarC0Sum A) (i : I) : ‖f i‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm (by simp) (toLp A f) i

/-- **Uniform bound for a c₀ norm.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras,
its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations and the
supremum norm. If `C ≥ 0` and `‖fᵢ‖ ≤ C` for every coordinate of a section `f`, then `‖f‖ ≤ C`,
including when the index set is empty. -/
theorem norm_le {f : CStarC0Sum A} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) : ‖f‖ ≤ C :=
  lp.norm_le_of_forall_le hC hf

/-- **Coordinate evaluation on a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. For each `i ∈ I`, evaluation `f ↦ fᵢ` is a nonunital complex star-algebra
homomorphism from the sum to `Aᵢ`. -/
def eval (i : I) : CStarC0Sum A →⋆ₙₐ[ℂ] A i where
  toFun f := f i
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

/-- **Evaluation formula on a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. The coordinate-evaluation homomorphism at `i` sends a section `f` to `fᵢ`. -/
@[simp]
theorem eval_apply (i : I) (f : CStarC0Sum A) : eval A i f = f i := rfl

/-- **Contractivity of c₀ evaluation.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Every coordinate evaluation satisfies `‖fᵢ‖ ≤ ‖f‖` for all c₀ sections `f`. -/
theorem norm_eval_le (i : I) (f : CStarC0Sum A) : ‖eval A i f‖ ≤ ‖f‖ :=
  norm_apply_le A f i

section Single

variable [DecidableEq I]

/-- **Vanishing of a single-coordinate section.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. For `i ∈ I` and `a ∈ Aᵢ`, the
bounded section that is `a` at `i` and zero elsewhere vanishes at cofinite. -/
theorem vanishes_lp_single (i : I) (a : A i) :
    VanishesAtCofinite (fun j => lp.single ∞ i a j) := by
  apply vanishes_of_finite_support
  refine (Set.finite_singleton i).subset fun j hj => ?_
  by_contra hji
  exact hj (by simpa using lp.single_apply_ne ∞ i a hji)

/-- **Single-coordinate inclusion into a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital
complex C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise
operations and the supremum norm. Assume that equality in `I` is decidable. For `i ∈ I`, the map
from `Aᵢ` to the sum that places its input at `i` and zero elsewhere is a nonunital complex star
homomorphism. -/
def single (i : I) : A i →⋆ₙₐ[ℂ] CStarC0Sum A where
  toFun a := ⟨lp.single ∞ i a, vanishes_lp_single A i a⟩
  map_zero' := by
    apply Subtype.ext
    exact lp.single_zero ∞ i
  map_add' a b := by
    apply Subtype.ext
    exact lp.single_add ∞ i a b
  map_mul' a b := by
    apply ext
    intro j
    change Pi.single i (a * b) j = Pi.single i a j * Pi.single i b j
    exact congrFun (Pi.single_mul i a b) j
  map_star' a := by
    apply ext
    intro j
    change Pi.single i (star a) j = star (Pi.single i a j)
    exact congrFun (Pi.single_star i a) j
  map_smul' c a := by
    apply Subtype.ext
    exact lp.single_smul ∞ i c a

/-- **Single-coordinate inclusion into ℓ∞.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. The inclusion into the bounded
product of the c₀ single-coordinate section at `i` agrees with the bounded-product single section at
`i`. -/
theorem toLp_single (i : I) (a : A i) :
    toLp A (single A i a) = lp.single ∞ i a := rfl

/-- **Coordinates of a single section.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. For `a ∈ Aᵢ`, the single-coordinate
section is `a` at `i` and zero at each other index, with the dependent fiber identified at `i`. -/
@[simp]
theorem single_apply (i : I) (a : A i) (j : I) :
    single A i a j = Pi.single i a j := rfl

/-- **Own coordinate of a single section.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. The single-coordinate inclusion of
`a ∈ Aᵢ`, evaluated at `i`, equals `a`. -/
@[simp]
theorem single_apply_self (i : I) (a : A i) : single A i a i = a :=
  lp.single_apply_self ∞ i a

/-- **Other coordinates of a single section.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. For `j ≠ i`, the single-coordinate
inclusion of `a ∈ Aᵢ` has value zero at `j`. -/
@[simp]
theorem single_apply_ne (i : I) (a : A i) {j : I} (hji : j ≠ i) :
    single A i a j = 0 :=
  lp.single_apply_ne ∞ i a hji

/-- **Norm of a single-coordinate section.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. The single-coordinate inclusion of
`a ∈ Aᵢ` has norm exactly `‖a‖`. -/
@[simp]
theorem norm_single (i : I) (a : A i) : ‖single A i a‖ = ‖a‖ :=
  lp.norm_single (by simp) i a

/-- **Isometric single-coordinate inclusion.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. For every `i ∈ I`, the
single-coordinate inclusion `Aᵢ → ⨁₀ Aᵢ` is an isometry. -/
theorem isometry_single (i : I) : Isometry (single A i) :=
  AddMonoidHomClass.isometry_of_norm (single A i) (norm_single A i)

/-- **Evaluation retracts a single inclusion.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. Inclusion of `Aᵢ` at coordinate `i`
followed by evaluation at `i` is the identity star homomorphism of `Aᵢ`. -/
@[simp]
theorem eval_comp_single (i : I) :
    (eval A i).comp (single A i) = NonUnitalStarAlgHom.id ℂ (A i) := by
  ext a
  exact single_apply_self A i a

/-- **Different evaluation annihilates a single inclusion.** For an arbitrary family `(Aᵢ)ᵢ∈I` of
nonunital complex C*-algebras, its c₀ direct sum consists of norm-vanishing sections with
coordinatewise operations and the supremum norm. Assume that equality in `I` is decidable. For `j ≠
i`, inclusion at `i` followed by evaluation at `j` is the zero star homomorphism from `Aᵢ` to `Aⱼ`. -/
theorem eval_comp_single_of_ne {i j : I} (hji : j ≠ i) :
    (eval A j).comp (single A i) = 0 := by
  ext a
  exact single_apply_ne A i a hji

end Single

section Truncation

variable [DecidableEq I]

/-- **Vanishing of finite coordinate cutoffs.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. For a finite subset `s ⊆ I` and c₀
section `f`, the section retaining `fᵢ` on `s` and zero outside `s` vanishes at cofinite. -/
theorem vanishes_cutoff (s : Finset I) (f : CStarC0Sum A) :
    VanishesAtCofinite (fun i => if i ∈ s then f i else 0) := by
  apply vanishes_of_finite_support
  refine s.finite_toSet.subset fun i hi => ?_
  by_contra hnot
  change i ∉ s at hnot
  change (if i ∈ s then f i else 0) ≠ 0 at hi
  rw [ite_eq_right hnot] at hi
  exact hi rfl

/-- **Finite-coordinate truncation of a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. For a finite subset `s ⊆ I`,
retaining coordinates in `s` and setting the rest to zero defines a nonunital complex star
endomorphism of the sum. -/
def truncate (s : Finset I) : CStarC0Sum A →⋆ₙₐ[ℂ] CStarC0Sum A where
  toFun f := ofFunction A (fun i => if i ∈ s then f i else 0)
    (vanishes_cutoff A s f)
  map_zero' := by ext i; simp
  map_add' f g := by ext i; by_cases hi : i ∈ s <;> simp [hi]
  map_mul' f g := by ext i; by_cases hi : i ∈ s <;> simp [hi]
  map_star' f := by ext i; by_cases hi : i ∈ s <;> simp [hi]
  map_smul' c f := by ext i; by_cases hi : i ∈ s <;> simp [hi]

/-- **Coordinates of a finite truncation.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. Truncation to a finite subset `s ⊆
I` has value `fᵢ` when `i ∈ s` and zero when `i ∉ s`. -/
@[simp]
theorem truncate_apply (s : Finset I) (f : CStarC0Sum A) (i : I) :
    truncate A s f i = if i ∈ s then f i else 0 := rfl

/-- **Retained coordinate under truncation.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. If `i` belongs to the finite
truncation set `s`, truncation of `f` has coordinate `fᵢ` at `i`. -/
theorem truncate_apply_of_mem (s : Finset I) (f : CStarC0Sum A) {i : I}
    (hi : i ∈ s) : truncate A s f i = f i := by simp [hi]

/-- **Omitted coordinate under truncation.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. If `i` does not belong to the
finite truncation set `s`, truncation of `f` has coordinate zero at `i`. -/
theorem truncate_apply_of_not_mem (s : Finset I) (f : CStarC0Sum A) {i : I}
    (hi : i ∉ s) : truncate A s f i = 0 := by simp [hi]

/-- **Finite support of truncation.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. For every finite `s ⊆ I` and
section `f`, truncation to `s` has finite support. -/
theorem finite_support_truncate (s : Finset I) (f : CStarC0Sum A) :
    Set.Finite {i : I | truncate A s f i ≠ 0} := by
  refine s.finite_toSet.subset fun i hi => ?_
  by_contra hnot
  change i ∉ s at hnot
  change truncate A s f i ≠ 0 at hi
  rw [truncate_apply, ite_eq_right hnot] at hi
  exact hi rfl

/-- **Composition of finite truncations.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. Truncation to a finite set `t`
followed by truncation to `s` equals truncation to `s ∩ t`. -/
theorem truncate_comp (s t : Finset I) :
    (truncate A s).comp (truncate A t) = truncate A (s ∩ t) := by
  ext f i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht]

/-- **Contractivity of truncation.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras,
its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations and the
supremum norm. Assume that equality in `I` is decidable. For every finite `s ⊆ I` and section `f`,
the norm of its truncation to `s` is at most `‖f‖`. -/
theorem norm_truncate_le (s : Finset I) (f : CStarC0Sum A) :
    ‖truncate A s f‖ ≤ ‖f‖ := by
  apply norm_le A (norm_nonneg _)
  intro i
  by_cases hi : i ∈ s
  · simpa [hi] using norm_apply_le A f i
  · simp [hi, norm_nonneg]

omit [DecidableEq I] in
/-- **Evaluation of a finite sum of c₀ sections.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital
complex C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise
operations and the supremum norm. For any finite set `s` in an index type `K` and family `f : K → ⨁₀
Aᵢ`, the `i` coordinate of `∑ k ∈ s, fₖ` is `∑ k ∈ s, (fₖ)ᵢ`. -/
@[simp]
theorem sum_apply {K : Type*} (s : Finset K) (f : K → CStarC0Sum A) (i : I) :
    (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i :=
  map_sum (eval A i) f s

/-- **Truncation as a sum of coordinate inclusions.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital
complex C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise
operations and the supremum norm. Assume that equality in `I` is decidable. For a finite `s ⊆ I`,
truncation of a section `f` equals `∑ i ∈ s, singleᵢ(fᵢ)`. -/
theorem truncate_eq_sum_single (s : Finset I) (f : CStarC0Sum A) :
    truncate A s f = ∑ i ∈ s, single A i (f i) := by
  apply ext
  intro j
  simp only [truncate_apply, sum_apply, single_apply, Finset.sum_pi_single]

/-- **Approximation by finite truncation.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. For every section `f` and `ε > 0`,
there is a finite `s ⊆ I` whose truncation satisfies `‖f - truncateₛ(f)‖ < ε`. -/
theorem exists_truncate_norm_sub_lt (f : CStarC0Sum A) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset I, ‖f - truncate A s f‖ < ε := by
  let s := (vanishes A f (ε / 2) (half_pos hε)).toFinset
  refine ⟨s, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  apply norm_le A (le_of_lt (half_pos hε))
  intro i
  by_cases hi : i ∈ s
  · simpa only [sub_apply, truncate_apply, ite_eq_left hi, sub_self, norm_zero]
      using (half_pos hε).le
  · have hsmall : ‖f i‖ < ε / 2 := by
      apply lt_of_not_ge
      intro hbad
      apply hi
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hbad
    simpa [hi] using hsmall.le

end Truncation

/-- **Finite-support sections in a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. This is the subset of sections for which `{i : fᵢ ≠ 0}` is finite. -/
def finiteSupportSet : Set (CStarC0Sum A) :=
  {f | Set.Finite {i : I | f i ≠ 0}}

/-- **Density of finite-support sections.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. The sections with finite support are dense in the c₀ sum for its supremum
norm. -/
theorem dense_finiteSupportSet : Dense (finiteSupportSet A) := by
  classical
  rw [Metric.dense_iff]
  intro f ε hε
  obtain ⟨s, hs⟩ := exists_truncate_norm_sub_lt A f hε
  refine ⟨truncate A s f, ?_, finite_support_truncate A s f⟩
  rw [Metric.mem_ball, dist_comm]
  simpa only [dist_eq_norm] using hs

/-- **Union of coordinate-inclusion ranges.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. This is the union over `i ∈ I` of
the images of the single-coordinate inclusions `Aᵢ → ⨁₀ Aᵢ`. -/
def singleRanges [DecidableEq I] : Set (CStarC0Sum A) :=
  ⋃ i : I, Set.range (single A i)

/-- **Truncations belong to the coordinate span.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital
complex C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise
operations and the supremum norm. Assume that equality in `I` is decidable. For every finite `s ⊆ I`
and section `f`, its truncation belongs to the complex-linear span of the coordinate-inclusion
ranges. -/
theorem truncate_mem_span_singleRanges [DecidableEq I]
    (s : Finset I) (f : CStarC0Sum A) :
    truncate A s f ∈ Submodule.span ℂ (singleRanges A) := by
  classical
  rw [truncate_eq_sum_single]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self (f i)⟩

/-- **Density of the coordinate span.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex
C*-algebras, its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations
and the supremum norm. Assume that equality in `I` is decidable. The complex-linear span of all
single-coordinate inclusion ranges is dense in the c₀ direct sum. -/
theorem dense_span_singleRanges [DecidableEq I] :
    Dense (Submodule.span ℂ (singleRanges A) : Set (CStarC0Sum A)) := by
  classical
  rw [Metric.dense_iff]
  intro f ε hε
  obtain ⟨s, hs⟩ := exists_truncate_norm_sub_lt A f hε
  refine ⟨truncate A s f, ?_, truncate_mem_span_singleRanges A s f⟩
  rw [Metric.mem_ball, dist_comm]
  simpa only [dist_eq_norm] using hs

section Separability

variable [Countable I] [∀ i, SeparableSpace (A i)]

/-- **Separability of the coordinate-inclusion ranges.** Let `I` be countable with decidable equality,
and let `(Aᵢ)ᵢ∈I` be separable nonunital complex C*-algebras. In their c₀ direct sum with supremum
norm, the union of the single-coordinate inclusion ranges is a separable subset. -/
theorem isSeparable_singleRanges [DecidableEq I] :
    TopologicalSpace.IsSeparable (singleRanges A) := by
  classical
  apply TopologicalSpace.IsSeparable.iUnion
  intro i
  exact TopologicalSpace.isSeparable_range (map_continuous (single A i))

/-- Output separability is derived from the actual dense complex span. -/
noncomputable instance instSeparableSpace : SeparableSpace (CStarC0Sum A) := by
  classical
  exact (dense_span_singleRanges A).isSeparable_iff.mp
    ((isSeparable_singleRanges A).span (R := ℂ))

end Separability

section FamilyMaps

variable (B : I → Type uB) [∀ i, NonUnitalCStarAlgebra (B i)]

/-- **Coordinatewise star map of c₀ sums.** Let `(Aᵢ)ᵢ∈I` and `(Bᵢ)ᵢ∈I` be arbitrary families of
nonunital complex C*-algebras, with c₀ sums in the supremum norm, and let `φᵢ : Aᵢ → Bᵢ` be
nonunital complex star homomorphisms. The formula `(aᵢ) ↦ (φᵢ(aᵢ))` defines a nonunital complex star
homomorphism between the two c₀ sums. -/
def map (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) :
    CStarC0Sum A →⋆ₙₐ[ℂ] CStarC0Sum B where
  toFun f := ofFunction B (fun i => φ i (f i))
    ((vanishes A f).of_norm_le_const_mul (K := 1) zero_lt_one
      (fun i => by simpa using NonUnitalStarAlgHom.norm_apply_le (φ i) (f i)))
  map_zero' := by ext i; simp
  map_add' f g := by ext i; simp
  map_mul' f g := by ext i; simp
  map_star' f := by
    apply ext
    intro i
    change φ i (star (f i)) = star (φ i (f i))
    exact map_star (φ i) (f i)
  map_smul' c f := by ext i; simp

/-- **Coordinates of the c₀ family map.** Let `(Aᵢ)ᵢ∈I` and `(Bᵢ)ᵢ∈I` be arbitrary families of nonunital
complex C*-algebras, with c₀ sums in the supremum norm, and let `φᵢ : Aᵢ → Bᵢ` be nonunital complex
star homomorphisms. The `i` coordinate of the image of a section `f` is `φᵢ(fᵢ)`. -/
@[simp]
theorem map_apply (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) (f : CStarC0Sum A) (i : I) :
    map A B φ f i = φ i (f i) := rfl

/-- **Contractivity of the c₀ family map.** Let `(Aᵢ)ᵢ∈I` and `(Bᵢ)ᵢ∈I` be arbitrary families of
nonunital complex C*-algebras, with c₀ sums in the supremum norm, and let `φᵢ : Aᵢ → Bᵢ` be
nonunital complex star homomorphisms. The coordinatewise map satisfies `‖map(φ)(f)‖ ≤ ‖f‖` for every
section `f`. -/
theorem norm_map_le (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) (f : CStarC0Sum A) :
    ‖map A B φ f‖ ≤ ‖f‖ :=
  NonUnitalStarAlgHom.norm_apply_le (map A B φ) f

/-- **Evaluation commutes with a c₀ family map.** Let `(Aᵢ)ᵢ∈I` and `(Bᵢ)ᵢ∈I` be arbitrary families of
nonunital complex C*-algebras, with c₀ sums in the supremum norm, and let `φᵢ : Aᵢ → Bᵢ` be
nonunital complex star homomorphisms. The family map followed by evaluation at `i` equals evaluation
at `i` followed by `φᵢ`. -/
theorem eval_comp_map (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) (i : I) :
    (eval B i).comp (map A B φ) = (φ i).comp (eval A i) := by
  ext f
  rfl

/-- **Identity map on a c₀ sum.** For an arbitrary family `(Aᵢ)ᵢ∈I` of nonunital complex C*-algebras,
its c₀ direct sum consists of norm-vanishing sections with coordinatewise operations and the
supremum norm. Applying the identity nonunital star homomorphism in every fiber gives the identity
homomorphism of the c₀ sum. -/
theorem map_id :
    map A A (fun i => NonUnitalStarAlgHom.id ℂ (A i)) =
      NonUnitalStarAlgHom.id ℂ (CStarC0Sum A) := by
  ext f i
  rfl

variable (C : I → Type uC) [∀ i, NonUnitalCStarAlgebra (C i)]

/-- **Composition of c₀ family maps.** For three arbitrary families `(Aᵢ),(Bᵢ),(Cᵢ)` of nonunital
complex C*-algebras and nonunital star homomorphisms `φᵢ : Aᵢ → Bᵢ`, `ψᵢ : Bᵢ → Cᵢ`, the c₀ family
map of `(ψᵢ ∘ φᵢ)ᵢ` equals the composition of the c₀ family map of `φ` with that of `ψ`, on the
supremum-norm c₀ sums. -/
theorem map_comp (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) (ψ : ∀ i, B i →⋆ₙₐ[ℂ] C i) :
    map A C (fun i => (ψ i).comp (φ i)) =
      (map B C ψ).comp (map A B φ) := by
  ext f i
  rfl

end FamilyMaps

end CStarC0Sum
