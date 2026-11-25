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
public import MathlibExt.Analysis.CStarAlgebra.SeparatedCompletion

/-!
# The actual separated completion of a C-star seminorm

An actual seminorm on an original unital complex star algebra determines
its seminormed ring and normed algebra structures. The original involution
is isometric for this computed norm. Separating and completing that same
seminorm produces a complete C-star algebra and its canonical unital
star-algebra homomorphism, with exactly the original seminorm values.

No norm, complete model, faithfulness, source separation, norm-one property
or nontriviality is supplied. The zero seminorm is permitted. All dictionaries
are explicit locally activated values, with no global instances.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarSeminorm

universe u

variable {B : Type u} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

/-- **Complex algebra structure for a C*-seminorm.** Let `B` be a unital complex star algebra with
scalar-compatible involution, and let `p` be a C*-seminorm on `B`. Equipping `B` with seminorm `p`
gives a seminormed complex algebra with its original multiplication and scalar action. -/
@[instance_reducible]
def sourceNormedAlgebra (p : CStarSeminorm B) :
    let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
    NormedAlgebra ℂ B := by
  let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
  exact
    { toAlgebra := ‹Algebra ℂ B›
      norm_smul_le := fun c x => by
        change p (c • x) ≤ ‖c‖ * p x
        exact (map_smul_eq_mul p c x).le }

/-- **Isometric involution for a C*-seminorm.** Let `B` be a unital complex star algebra with
scalar-compatible involution, and let `p` be a C*-seminorm on `B`. The involution of `B` preserves
distances for the seminorm induced by `p`. -/
theorem sourceNormedStarGroup (p : CStarSeminorm B) :
    let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
    NormedStarGroup B := by
  let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
  exact
    { norm_star_le := fun x => by
        change p (star x) ≤ p x
        exact (p.map_star x).le }

/-- **Separated C*-seminorm completion.** Let `B` be a unital complex star algebra with
scalar-compatible involution, and let `p` be a C*-seminorm on `B`. This is the uniform completion of
the separation quotient of `B` for `p`, identifying elements at seminorm distance zero before
completing. -/
abbrev Completion (p : CStarSeminorm B) : Type u :=
  let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
  UniformSpace.Completion (SeparationQuotient B)

/-- **C*-structure on a seminorm completion.** Let `B` be a unital complex star algebra with
scalar-compatible involution, and let `p` be a C*-seminorm on `B`. The separated completion for `p`
is a unital complex C*-algebra with the extended multiplication, scalar action, and involution. -/
@[instance_reducible]
def completionCStarAlgebra (p : CStarSeminorm B) : CStarAlgebra p.Completion := by
  let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
  let _ : NormedAlgebra ℂ B := p.sourceNormedAlgebra
  let _ : NormedStarGroup B := p.sourceNormedStarGroup
  change CStarAlgebra (UniformSpace.Completion (SeparationQuotient B))
  exact CStarAlgebra.separatedCompletionCStarAlgebra B (by
    intro x
    change p x * p x ≤ p (star x * x)
    simpa only [pow_two] using (p.map_star_mul_self x).ge)

/-- **Star homomorphism into a C*-seminorm completion.** Let `B` be a unital complex star algebra with
scalar-compatible involution, and let `p` be a C*-seminorm on `B`. The canonical map from `B` to its
separated completion is a unital complex star-algebra homomorphism. -/
def toCompletion (p : CStarSeminorm B) :
    let _ : CStarAlgebra p.Completion := p.completionCStarAlgebra
    B →⋆ₐ[ℂ] p.Completion := by
  let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
  let _ : NormedAlgebra ℂ B := p.sourceNormedAlgebra
  let _ : NormedStarGroup B := p.sourceNormedStarGroup
  have hCStar : ∀ x : B, ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
    intro x
    change p x * p x ≤ p (star x * x)
    simpa only [pow_two] using (p.map_star_mul_self x).ge
  let _ : CStarAlgebra (UniformSpace.Completion (SeparationQuotient B)) :=
    CStarAlgebra.separatedCompletionCStarAlgebra B hCStar
  change B →⋆ₐ[ℂ] UniformSpace.Completion (SeparationQuotient B)
  exact CStarAlgebra.separatedCompletionStarAlgHom B hCStar

/-- **Canonical map into a seminorm completion.** Let `B` be a unital complex star algebra with
scalar-compatible involution, and let `p` be a C*-seminorm on `B`. For every `x ∈ B`, the canonical
map is the separation-quotient class of `x` followed by the dense inclusion into the uniform
completion. -/
@[simp]
theorem toCompletion_apply (p : CStarSeminorm B) (x : B) :
    let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
    let _ : CStarAlgebra p.Completion := p.completionCStarAlgebra
    p.toCompletion x = ((SeparationQuotient.mk x : SeparationQuotient B) : p.Completion) :=
  rfl

/-- **Completion norm equals the source seminorm.** Let `B` be a unital complex star algebra with
scalar-compatible involution, and let `p` be a C*-seminorm on `B`. For every `x ∈ B`, its canonical
image in the separated completion has norm `p(x)`. -/
theorem norm_toCompletion (p : CStarSeminorm B) (x : B) :
    let _ : CStarAlgebra p.Completion := p.completionCStarAlgebra
    ‖p.toCompletion x‖ = p x := by
  let _ : SeminormedRing B := p.toRingSeminorm.toSeminormedRing
  let _ : NormedAlgebra ℂ B := p.sourceNormedAlgebra
  let _ : NormedStarGroup B := p.sourceNormedStarGroup
  let _ : CStarAlgebra p.Completion := p.completionCStarAlgebra
  have hCStar : ∀ a : B, ‖a‖ * ‖a‖ ≤ ‖star a * a‖ := by
    intro a
    change p a * p a ≤ p (star a * a)
    simpa only [pow_two] using (p.map_star_mul_self a).ge
  have hrawNorm : ‖x‖ = p x := by
    change p.toRingSeminorm x = p x
    exact p.toRingSeminorm_apply x
  have hnorm : ‖CStarAlgebra.separatedCompletionStarAlgHom B hCStar x‖ = p x :=
    (CStarAlgebra.separatedCompletionStarAlgHom_norm B hCStar x).trans hrawNorm
  dsimp only [toCompletion, Completion, completionCStarAlgebra]
  simpa only [id_eq] using hnorm

end CStarSeminorm
