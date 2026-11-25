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

public import MathlibExt.Analysis.CStarAlgebra.Seminorm
public import MathlibExt.Analysis.CStarAlgebra.NonUnitalSeparationQuotient
public import MathlibExt.Analysis.CStarAlgebra.NonUnitalCompletion

/-!
# The actual nonunital completion of a C-star seminorm

The original nonunital ring and complex module retain their operations.
Only the norm and pseudometric are computed from the actual C-star seminorm.
Its literal separation quotient receives the stock normed ring and scalar
structures and the shared descended involution. The C-star square law is
used on that quotient, followed by the existing ordinary nonunital C-star
completion. The canonical map is quotient mk followed by completion coe.

The zero seminorm is permitted. All dictionaries are explicit local values.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarSeminorm

universe u

variable {B : Type u} [NonUnitalRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarRing B] [StarModule ℂ B]

/-- **Seminormed ring induced by a C*-seminorm.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. The seminorm `p` defines a
nonunital seminormed ring structure on the given ring, with distance `p(x-y)`. -/
@[instance_reducible]
def sourceNonUnitalSeminormedRing (p : CStarSeminorm B) : NonUnitalSeminormedRing B where
  __ := ‹NonUnitalRing B›
  __ := p.toRingSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup
  norm_mul_le := p.mul_le'

/-- **Complex seminormed space induced by a C*-seminorm.** Let `B` be a nonunital complex star algebra
with scalar-compatible involution and let `p` be a C*-seminorm on `B`. The seminorm `p` defines a
compatible complex seminormed vector-space structure on the given module. -/
@[instance_reducible]
def sourceNonUnitalNormedSpace (p : CStarSeminorm B) :
    let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
    NormedSpace ℂ B := by
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  exact
    { toModule := ‹Module ℂ B›
      norm_smul_le := fun c x => by
        change p (c • x) ≤ ‖c‖ * p x
        exact (map_smul_eq_mul p c x).le }

/-- **Separated nonunital C*-completion.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. This is the uniform completion of
the separation quotient for `p`, first identifying elements at seminorm distance zero. -/
abbrev NonUnitalCompletion (p : CStarSeminorm B) : Type u :=
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  UniformSpace.Completion (SeparationQuotient B)

/-- **C*-structure of a nonunital seminorm completion.** Let `B` be a nonunital complex star algebra
with scalar-compatible involution and let `p` be a C*-seminorm on `B`. The separated completion is a
nonunital complex C*-algebra with the norm and operations induced by `p`. -/
@[instance_reducible]
def nonUnitalCompletionCStarAlgebra (p : CStarSeminorm B) :
    NonUnitalCStarAlgebra p.NonUnitalCompletion := by
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  let _ : NormedSpace ℂ B := p.sourceNonUnitalNormedSpace
  let _ : NormedStarGroup B :=
    { norm_star_le := fun x => by
        change p (star x) ≤ p x
        exact (p.map_star x).le }
  let _ : StarRing (SeparationQuotient B) := SeparationQuotient.nonUnitalCstarStarRing B
  let _ : StarModule ℂ (SeparationQuotient B) := SeparationQuotient.nonUnitalCstarStarModule B
  let _ : CStarRing (SeparationQuotient B) := SeparationQuotient.nonUnitalCstarRing B (by
    intro x
    change p x * p x ≤ p (star x * x)
    simpa only [pow_two] using (p.map_star_mul_self x).ge)
  let _ : IsScalarTower ℂ (SeparationQuotient B) (SeparationQuotient B) := by
    refine { smul_assoc := ?_ }
    intro c x y
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
    change (c • SeparationQuotient.mk a) * SeparationQuotient.mk b =
      c • (SeparationQuotient.mk a * SeparationQuotient.mk b)
    simpa only [← SeparationQuotient.mk_smul, ← SeparationQuotient.mk_mul] using
      congrArg (SeparationQuotient.mk : B → SeparationQuotient B) (smul_mul_assoc c a b)
  let _ : SMulCommClass ℂ (SeparationQuotient B) (SeparationQuotient B) := by
    refine { smul_comm := ?_ }
    intro c x y
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
    change c • (SeparationQuotient.mk a * SeparationQuotient.mk b) =
      SeparationQuotient.mk a * (c • SeparationQuotient.mk b)
    simpa only [← SeparationQuotient.mk_mul, ← SeparationQuotient.mk_smul] using
      congrArg (SeparationQuotient.mk : B → SeparationQuotient B) (mul_smul_comm c a b).symm
  change NonUnitalCStarAlgebra (UniformSpace.Completion (SeparationQuotient B))
  exact CStarAlgebra.completionNonUnitalCStarAlgebra (SeparationQuotient B)

/-- **Canonical map into a nonunital C*-completion.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. The separation projection followed
by the completion inclusion defines a nonunital complex star homomorphism from `B` to its separated
completion. -/
def toNonUnitalCompletion (p : CStarSeminorm B) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    B →⋆ₙₐ[ℂ] p.NonUnitalCompletion := by
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  let _ : NormedSpace ℂ B := p.sourceNonUnitalNormedSpace
  let _ : NormedStarGroup B :=
    { norm_star_le := fun x => by
        change p (star x) ≤ p x
        exact (p.map_star x).le }
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  change B →⋆ₙₐ[ℂ] UniformSpace.Completion (SeparationQuotient B)
  exact
    { toFun := fun x => ((SeparationQuotient.mk x : SeparationQuotient B) :
          UniformSpace.Completion (SeparationQuotient B))
      map_zero' := by
        change ((SeparationQuotient.mk (0 : B) : SeparationQuotient B) :
          UniformSpace.Completion (SeparationQuotient B)) = 0
        rw [SeparationQuotient.mk_zero, UniformSpace.Completion.coe_zero]
      map_add' := fun x y => by
        change ((SeparationQuotient.mk (x + y) : SeparationQuotient B) :
          UniformSpace.Completion (SeparationQuotient B)) =
            ((SeparationQuotient.mk x : SeparationQuotient B) :
              UniformSpace.Completion (SeparationQuotient B)) +
            ((SeparationQuotient.mk y : SeparationQuotient B) :
              UniformSpace.Completion (SeparationQuotient B))
        rw [SeparationQuotient.mk_add, UniformSpace.Completion.coe_add]
      map_smul' := fun c x => by
        change ((SeparationQuotient.mk (c • x) : SeparationQuotient B) :
          UniformSpace.Completion (SeparationQuotient B)) =
            c • ((SeparationQuotient.mk x : SeparationQuotient B) :
              UniformSpace.Completion (SeparationQuotient B))
        rw [SeparationQuotient.mk_smul, UniformSpace.Completion.coe_smul]
      map_mul' := fun x y => by
        rw [SeparationQuotient.mk_mul,
          UniformSpace.Completion.nonUnitalCompletion_coe_mul (SeparationQuotient B)]
      map_star' := fun x => by
        change ((SeparationQuotient.mk (star x) : SeparationQuotient B) :
          UniformSpace.Completion (SeparationQuotient B)) =
            UniformSpace.Completion.map (SeparationQuotient.map (star : B → B))
              ((SeparationQuotient.mk x : SeparationQuotient B) :
                UniformSpace.Completion (SeparationQuotient B))
        rw [UniformSpace.Completion.map_coe
            (SeparationQuotient.uniformContinuous_map (star : B → B)),
          SeparationQuotient.map_mk star_isometry.uniformContinuous] }

/-- **Formula for the nonunital completion map.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. For every `x ∈ B`, its canonical
image is the separation class of `x` followed by inclusion into the uniform completion. -/
@[simp]
theorem toNonUnitalCompletion_apply (p : CStarSeminorm B) (x : B) :
    let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.toNonUnitalCompletion x =
      ((SeparationQuotient.mk x : SeparationQuotient B) : p.NonUnitalCompletion) :=
  rfl

/-- **Norm in a nonunital C*-completion.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. The canonical completion image of
`x ∈ B` has norm `p(x)`. -/
theorem norm_toNonUnitalCompletion (p : CStarSeminorm B) (x : B) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    ‖p.toNonUnitalCompletion x‖ = p x := by
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  calc
    ‖p.toNonUnitalCompletion x‖ = ‖x‖ := by
      rw [toNonUnitalCompletion_apply, UniformSpace.Completion.norm_coe, SeparationQuotient.norm_mk]
    _ = p x := rfl

/-- **Null kernel of the nonunital completion map.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. The completion image of `x ∈ B` is
zero exactly when `p(x) = 0`. -/
theorem toNonUnitalCompletion_eq_zero_iff (p : CStarSeminorm B) (x : B) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    p.toNonUnitalCompletion x = 0 ↔ p x = 0 := by
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  rw [← norm_eq_zero, norm_toNonUnitalCompletion]

/-- **Dense range of the canonical completion map.** Let `B` be a nonunital complex star algebra with
scalar-compatible involution and let `p` be a C*-seminorm on `B`. The nonunital star homomorphism
from `B` into its separated completion has norm-dense range. -/
theorem denseRange_toNonUnitalCompletion (p : CStarSeminorm B) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    DenseRange p.toNonUnitalCompletion := by
  let _ : NonUnitalSeminormedRing B := p.sourceNonUnitalSeminormedRing
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  have hfun : (p.toNonUnitalCompletion : B → p.NonUnitalCompletion) =
      (fun x : B => ((SeparationQuotient.mk x : SeparationQuotient B) : p.NonUnitalCompletion)) :=
    funext (toNonUnitalCompletion_apply p)
  rw [hfun]
  have hrange : Set.range (fun x : B =>
      ((SeparationQuotient.mk x : SeparationQuotient B) : p.NonUnitalCompletion)) =
      Set.range ((↑) : SeparationQuotient B → p.NonUnitalCompletion) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨SeparationQuotient.mk x, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk q
      exact ⟨x, rfl⟩
  change Dense (Set.range (fun x : B =>
    ((SeparationQuotient.mk x : SeparationQuotient B) : p.NonUnitalCompletion)))
  rw [hrange]
  exact UniformSpace.Completion.denseRange_coe

end CStarSeminorm
