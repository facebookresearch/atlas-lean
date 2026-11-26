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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Pullback of a normal action through a continuous homomorphism

Let `G,D` be groups with topologies and `f : G → D` a continuous homomorphism. If `β : D →
Aut_normal(M)` is a normal action with norm-continuous inverse predual orbits, its pullback is
`α_g=β_(f(g))`.

The inverse functional orbit is `φ∘β_(f(g))⁻¹`, and its norm continuity is the composition of
the orbit map with `f`. No continuity of the group multiplication or inverse is required for
this pullback.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uD uH

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {D : Type uD} [Group D] [TopologicalSpace D]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- **Normal action pulled back by a continuous group homomorphism.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. let `G,D` be groups with topologies, `β :
NormalAction D M` and `f : G →ₜ* D` a continuous homomorphism. Then `comp β f :
NormalAction G M` has action `g ↦ β_(f(g))` and the corresponding norm-continuous inverse
predual orbits. -/
def comp (β : NormalAction D M) (f : G →ₜ* D) : NormalAction G M where
  toMonoidHom := β.toMonoidHom.comp f.toMonoidHom
  continuous_predual_orbit φ := (β.continuous_predual_orbit φ).comp f.continuous

/-- **Automorphism value of a pulled-back normal action.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. for groups `G,D` with topologies, normal action `β` of `D`, continuous homomorphism
`f : G → D` and `g ∈ G`, `comp β f g=β(f(g))`. -/
@[simp]
theorem comp_apply (β : NormalAction D M) (f : G →ₜ* D) (g : G) :
    comp β f g = β (f g) :=
  rfl

end

end VonNeumannAlgebra.NormalAction
