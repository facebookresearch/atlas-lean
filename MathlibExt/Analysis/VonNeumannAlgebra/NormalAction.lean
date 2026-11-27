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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalEquiv

/-!
# Normal automorphism actions with norm-continuous predual orbits

For a concrete von Neumann algebra `M` and a group `G` with a topology, a normal action is a
homomorphism `α : G → Aut_normal(M)` for which `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for
every normal functional `φ`. The functional norm is inherited from the continuous dual of `M`.

The induced predual action is `g·φ=φ∘α_g⁻¹`; its evaluation is `(g·φ)(x)=φ(α_g⁻¹(x))`. Every
algebra automorphism `α_g` is ultraweakly continuous. Continuity of the group operations is not
part of this bundle's assumptions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe uG uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Normal action with norm-continuous inverse predual orbits.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. for a group `G` with a topology, `NormalAction G M`
contains a homomorphism `α : G → Aut_normal(M)` and norm continuity of `g ↦ φ∘α_g⁻¹` in
`M_*` for each `φ ∈ M_*`. -/
structure NormalAction (G : Type uG) [Group G] [TopologicalSpace G]
    (M : VonNeumannAlgebra H) where
  /-- **Normal-automorphism homomorphism of the group action.** Let `H` be a complete complex
  Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩`
  for its vector functionals. Let `M_*` be their norm-closed complex span in the
  continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦
  φ(x)` for `φ ∈ M_*`. for a group `G` with a topology, the action field is a homomorphism
  `α : G → Aut_normal(M)`, with `α_(gh)=α_g∘α_h` and `α_1=id_M`. -/
  toMonoidHom : G →* NormalStarAlgEquiv M M
  /-- **Norm continuity of each inverse functional orbit.** Let `H` be a complete complex
  Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩`
  for its vector functionals. Let `M_*` be their norm-closed complex span in the
  continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦
  φ(x)` for `φ ∈ M_*`. for the action homomorphism `α : G → Aut_normal(M)` on a group with
  topology, `g ↦ φ∘α_g⁻¹` is continuous in the Banach norm of `M_*` for each `φ ∈ M_*`. -/
  continuous_predual_orbit : ∀ φ : normalFunctionalSpace M,
    Continuous fun g : G => NormalStarAlgEquiv.predualActionHom M (toMonoidHom g) φ

namespace NormalAction

variable {G : Type uG} [Group G] [TopologicalSpace G] {M : VonNeumannAlgebra H}

/-- **Normal action equality from its automorphism homomorphism.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`,
induced by `x ↦ φ(x)` for `φ ∈ M_*`. two normal actions of a group `G` with topology are
equal when their homomorphisms `G → Aut_normal(M)` are equal. -/
@[ext]
theorem ext {α β : NormalAction G M} (h : α.toMonoidHom = β.toMonoidHom) : α = β := by
  cases α
  cases β
  cases h
  rfl

@[macro_inline]
instance : FunLike (NormalAction G M) G (NormalStarAlgEquiv M M) where
  coe α := α.toMonoidHom
  coe_injective α β h := by
    have hmap : α.toMonoidHom = β.toMonoidHom :=
      DFunLike.ext _ _ fun g => congrFun h g
    exact ext hmap

instance : MonoidHomClass (NormalAction G M) G (NormalStarAlgEquiv M M) where
  map_one α := α.toMonoidHom.map_one
  map_mul α := α.toMonoidHom.map_mul

/-- **Value of the normal action homomorphism.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. Let
`G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such that `g ↦
φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. for `g ∈ G`, `α.toMonoidHom
g=α_g`. -/
@[simp]
theorem toMonoidHom_apply (α : NormalAction G M) (g : G) : α.toMonoidHom g = α g :=
  rfl

/-- **Underlying complex star-automorphism action.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such
that `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. `α.toStarAlgAutHom : G
→ Aut_star(M)` retains the algebra automorphisms `α_g`, forgetting the continuity
properties. -/
def toStarAlgAutHom (α : NormalAction G M) : G →* (M ≃⋆ₐ[ℂ] M) :=
  (NormalStarAlgEquiv.toStarAlgAutHom M).comp α.toMonoidHom

/-- **Algebra value of the normal group action.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. Let
`G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such that `g ↦
φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. for `g ∈ G` and `x ∈ M`,
`α.toStarAlgAutHom g x=α_g(x)`. -/
@[simp]
theorem toStarAlgAutHom_apply (α : NormalAction G M) (g : G) (x : M) :
    α.toStarAlgAutHom g x = α g x :=
  rfl

/-- **Ultraweak continuity of each action automorphism.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such
that `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. for every fixed `g ∈
G`, `x ↦ α_g(x)` is continuous on `M` with its ultraweak topology. -/
theorem continuous_ultraweak (α : NormalAction G M) (g : G) :
    Continuous fun x : Ultraweak M =>
      (ultraweakLinearEquiv M).symm (α g (ultraweakLinearEquiv M x)) :=
  (α g).continuous_ultraweak

/-- **Covariant action on the normal-functional Banach space.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such
that `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. `α.predualAction : G →
Aut_CLM(M_*)` is the homomorphism `g ↦ (φ ↦ φ∘α_g⁻¹)`. -/
def predualAction (α : NormalAction G M) :
    G →* (normalFunctionalSpace M ≃L[ℂ] normalFunctionalSpace M) :=
  (NormalStarAlgEquiv.predualActionHom M).comp α.toMonoidHom

/-- **Inverse-automorphism evaluation of the predual action.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such
that `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. for `g ∈ G`, `φ ∈ M_*`
and `x ∈ M`, `(α.predualAction g φ)(x)=φ(α_g⁻¹(x))`. -/
@[simp]
theorem predualAction_apply (α : NormalAction G M) (g : G)
    (φ : normalFunctionalSpace M) (x : M) :
    (α.predualAction g φ : StrongDual ℂ M) x = (φ : StrongDual ℂ M) ((α g).symm x) :=
  NormalStarAlgEquiv.predualActionHom_apply (α g) φ x

/-- **Norm-continuous orbit of every normal functional.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `G` be a group with a topology and `α : G → Aut_normal(M)` a homomorphism such
that `g ↦ φ∘α_g⁻¹` is norm-continuous in `M_*` for every `φ ∈ M_*`. for every `φ ∈ M_*`,
the map `g ↦ α.predualAction g φ` is continuous in the inherited continuous-dual norm. -/
theorem predualAction_continuous (α : NormalAction G M) (φ : normalFunctionalSpace M) :
    Continuous fun g : G => α.predualAction g φ :=
  α.continuous_predual_orbit φ

end NormalAction

end

end VonNeumannAlgebra
