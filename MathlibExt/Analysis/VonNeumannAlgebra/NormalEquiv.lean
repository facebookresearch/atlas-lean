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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Normal equivalences and their actions on normal functionals

A normal equivalence `f : M ≃ N` of concrete von Neumann algebras is a complex star-algebra
equivalence whose forward and inverse maps are ultraweakly continuous. Identities, inverses and
composition give the group of normal automorphisms, with `(f*g)(x)=f(g(x))`.

Functional pullback is the continuous linear equivalence `f_* : N_* ≃ M_*`, `φ ↦ φ∘f`. For
automorphisms, inverse pullback is the covariant action `f·φ=φ∘f⁻¹`, forming a group
homomorphism to continuous linear automorphisms of `M_*`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Star-algebra equivalence continuous ultraweakly in both directions.** Let `M,N` be
concrete von Neumann algebras on complete complex Hilbert spaces. Their normal-functional
Banach spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their
ultraweak topologies are `σ(M,M_*)`, `σ(N,N_*)`. `NormalStarAlgEquiv M N` contains a
complex star-algebra equivalence `f : M ≃ N` whose forward and inverse maps are
ultraweakly continuous. -/
structure NormalStarAlgEquiv (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) where
  /-- **Underlying star equivalence of a normal isomorphism.** Let `M,N` be concrete von
  Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
  spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
  topologies are `σ(M,M_*)`, `σ(N,N_*)`. the field is `f : M ≃⋆ₐ[ℂ] N`, a complex
  star-algebra equivalence of the concrete carriers. -/
  toStarAlgEquiv : M ≃⋆ₐ[ℂ] N
  /-- **Ultraweak continuity of the forward normal equivalence.** Let `M,N` be concrete von
  Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
  spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
  topologies are `σ(M,M_*)`, `σ(N,N_*)`. the forward map `f : M → N` is continuous from
  `σ(M,M_*)` to `σ(N,N_*)`. -/
  continuous_ultraweak :
    Continuous fun x : Ultraweak M =>
      (ultraweakLinearEquiv N).symm (toStarAlgEquiv (ultraweakLinearEquiv M x))
  /-- **Ultraweak continuity of the inverse normal equivalence.** Let `M,N` be concrete von
  Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
  spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
  topologies are `σ(M,M_*)`, `σ(N,N_*)`. the inverse map `f⁻¹ : N → M` is continuous from
  `σ(N,N_*)` to `σ(M,M_*)`. -/
  continuous_ultraweak_symm :
    Continuous fun x : Ultraweak N =>
      (ultraweakLinearEquiv M).symm (toStarAlgEquiv.symm (ultraweakLinearEquiv N x))

namespace NormalStarAlgEquiv

variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- **Normal equivalence equality from its star-algebra map.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. normal equivalences with equal underlying complex star-algebra
equivalences are equal. -/
@[ext]
theorem ext {f g : NormalStarAlgEquiv M N}
    (h : f.toStarAlgEquiv = g.toStarAlgEquiv) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : EquivLike (NormalStarAlgEquiv M N) M N where
  coe f := f.toStarAlgEquiv
  inv f := f.toStarAlgEquiv.symm
  left_inv f := f.toStarAlgEquiv.left_inv
  right_inv f := f.toStarAlgEquiv.right_inv
  coe_injective' f g h _ := by
    have hmap : f.toStarAlgEquiv = g.toStarAlgEquiv :=
      DFunLike.ext _ _ fun x => congrFun h x
    exact ext hmap

instance : Coe (NormalStarAlgEquiv M N) (M ≃⋆ₐ[ℂ] N) := ⟨toStarAlgEquiv⟩

instance : AlgEquivClass (NormalStarAlgEquiv M N) ℂ M N where
  map_mul f := map_mul f.toStarAlgEquiv
  map_add f := map_add f.toStarAlgEquiv
  commutes f := AlgHomClass.commutes f.toStarAlgEquiv

instance : StarHomClass (NormalStarAlgEquiv M N) M N where
  map_star f := map_star f.toStarAlgEquiv

/-- **Underlying star-equivalence value.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence, ultraweakly continuous
in both directions. for `x ∈ M`, `f.toStarAlgEquiv x=f(x)`. -/
@[simp]
theorem toStarAlgEquiv_apply (f : NormalStarAlgEquiv M N) (x : M) :
    f.toStarAlgEquiv x = f x :=
  rfl

/-- **Forward normal homomorphism of a normal equivalence.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence,
ultraweakly continuous in both directions. `f.toNormalStarAlgHom : M → N` retains the
forward unital complex star map and its ultraweak continuity. -/
def toNormalStarAlgHom (f : NormalStarAlgEquiv M N) : NormalStarAlgHom M N where
  toStarAlgHom := f.toStarAlgEquiv.toStarAlgHom
  continuous_ultraweak := f.continuous_ultraweak

/-- **Forward normal-map value of an equivalence.** Let `M,N` be concrete von Neumann algebras
on complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are
the norm-closed spans of vector functionals, and their ultraweak topologies are
`σ(M,M_*)`, `σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence, ultraweakly
continuous in both directions. for `x ∈ M`, `f.toNormalStarAlgHom x=f(x)`. -/
@[simp]
theorem toNormalStarAlgHom_apply (f : NormalStarAlgEquiv M N) (x : M) :
    f.toNormalStarAlgHom x = f x :=
  rfl

/-- **Identity normal star-algebra equivalence.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`.
`NormalStarAlgEquiv.refl M` is `x ↦ x` in both directions. -/
def refl (M : VonNeumannAlgebra H) : NormalStarAlgEquiv M M where
  toStarAlgEquiv := StarAlgEquiv.refl ℂ M
  continuous_ultraweak := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv M).symm
          (StarAlgEquiv.refl ℂ M (ultraweakLinearEquiv M x))) =
        (_root_.id : Ultraweak M → Ultraweak M) := by
      funext x
      change (ultraweakLinearEquiv M).symm (ultraweakLinearEquiv M x) = x
      exact (ultraweakLinearEquiv M).symm_apply_apply x
    rw [hfun]
    exact continuous_id
  continuous_ultraweak_symm := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv M).symm
          ((StarAlgEquiv.refl ℂ M).symm (ultraweakLinearEquiv M x))) =
        (_root_.id : Ultraweak M → Ultraweak M) := by
      funext x
      change (ultraweakLinearEquiv M).symm (ultraweakLinearEquiv M x) = x
      exact (ultraweakLinearEquiv M).symm_apply_apply x
    rw [hfun]
    exact continuous_id

/-- **Identity equivalence on a von Neumann element.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its
vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. for `x ∈ M`, `NormalStarAlgEquiv.refl M x=x`. -/
@[simp]
theorem refl_apply (x : M) : refl M x = x :=
  rfl

/-- **Inverse normal star-algebra equivalence.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence, ultraweakly continuous
in both directions. `f.symm : N ≃ M` has forward map `f⁻¹` and inverse map `f`, both
ultraweakly continuous. -/
def symm (f : NormalStarAlgEquiv M N) : NormalStarAlgEquiv N M where
  toStarAlgEquiv := f.toStarAlgEquiv.symm
  continuous_ultraweak := f.continuous_ultraweak_symm
  continuous_ultraweak_symm := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
          (f.toStarAlgEquiv.symm.symm (ultraweakLinearEquiv M x))) =
        (fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
          (f.toStarAlgEquiv (ultraweakLinearEquiv M x))) := by
      funext x
      exact congrArg (fun e : M ≃⋆ₐ[ℂ] N =>
        (ultraweakLinearEquiv N).symm (e (ultraweakLinearEquiv M x)))
        f.toStarAlgEquiv.symm_symm
    rw [hfun]
    exact f.continuous_ultraweak

/-- **Value of the inverse normal equivalence.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence, ultraweakly continuous
in both directions. for `y ∈ N`, `f.symm y=f.toStarAlgEquiv.symm y=f⁻¹(y)`. -/
theorem symm_apply (f : NormalStarAlgEquiv M N) (x : N) :
    f.symm x = f.toStarAlgEquiv.symm x :=
  rfl

/-- **Normal inverse recovers a source element.** Let `M,N` be concrete von Neumann algebras
on complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are
the norm-closed spans of vector functionals, and their ultraweak topologies are
`σ(M,M_*)`, `σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence, ultraweakly
continuous in both directions. for `x ∈ M`, `f.symm (f(x))=x`. -/
@[simp]
theorem symm_apply_apply (f : NormalStarAlgEquiv M N) (x : M) : f.symm (f x) = x :=
  f.toStarAlgEquiv.symm_apply_apply x

/-- **Normal forward map recovers a target element.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence,
ultraweakly continuous in both directions. for `y ∈ N`, `f(f.symm y)=y`. -/
@[simp]
theorem apply_symm_apply (f : NormalStarAlgEquiv M N) (x : N) : f (f.symm x) = x :=
  f.toStarAlgEquiv.apply_symm_apply x

/-- **Double inverse of a normal equivalence.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence, ultraweakly continuous
in both directions. `f.symm.symm=f`. -/
@[simp]
theorem symm_symm (f : NormalStarAlgEquiv M N) : f.symm.symm = f := by
  apply ext
  exact f.toStarAlgEquiv.symm_symm

variable {L : Type w} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {P : VonNeumannAlgebra L}

/-- **Composition of normal star-algebra equivalences.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence,
ultraweakly continuous in both directions. for a normal equivalence `g : N ≃ P` to another
concrete von Neumann algebra, `f.trans g : M ≃ P` has forward map `g∘f` and inverse map
`f⁻¹∘g⁻¹`. -/
def trans (f : NormalStarAlgEquiv M N) (g : NormalStarAlgEquiv N P) :
    NormalStarAlgEquiv M P where
  toStarAlgEquiv := f.toStarAlgEquiv.trans g.toStarAlgEquiv
  continuous_ultraweak := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv P).symm
          ((f.toStarAlgEquiv.trans g.toStarAlgEquiv) (ultraweakLinearEquiv M x))) =
        ((fun y : Ultraweak N => (ultraweakLinearEquiv P).symm
          (g.toStarAlgEquiv (ultraweakLinearEquiv N y))) ∘
          fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
            (f.toStarAlgEquiv (ultraweakLinearEquiv M x))) := by
      funext x
      change (ultraweakLinearEquiv P).symm
          (g.toStarAlgEquiv (f.toStarAlgEquiv (ultraweakLinearEquiv M x))) =
        (ultraweakLinearEquiv P).symm (g.toStarAlgEquiv (ultraweakLinearEquiv N
          ((ultraweakLinearEquiv N).symm (f.toStarAlgEquiv (ultraweakLinearEquiv M x)))))
      exact congrArg (fun y : N => (ultraweakLinearEquiv P).symm (g.toStarAlgEquiv y))
        ((ultraweakLinearEquiv N).apply_symm_apply
          (f.toStarAlgEquiv (ultraweakLinearEquiv M x))).symm
    rw [hfun]
    exact g.continuous_ultraweak.comp f.continuous_ultraweak
  continuous_ultraweak_symm := by
    have hfun :
        (fun x : Ultraweak P => (ultraweakLinearEquiv M).symm
          ((f.toStarAlgEquiv.trans g.toStarAlgEquiv).symm (ultraweakLinearEquiv P x))) =
        ((fun y : Ultraweak N => (ultraweakLinearEquiv M).symm
          (f.toStarAlgEquiv.symm (ultraweakLinearEquiv N y))) ∘
          fun x : Ultraweak P => (ultraweakLinearEquiv N).symm
            (g.toStarAlgEquiv.symm (ultraweakLinearEquiv P x))) := by
      funext x
      change (ultraweakLinearEquiv M).symm
          (f.toStarAlgEquiv.symm (g.toStarAlgEquiv.symm (ultraweakLinearEquiv P x))) =
        (ultraweakLinearEquiv M).symm (f.toStarAlgEquiv.symm (ultraweakLinearEquiv N
          ((ultraweakLinearEquiv N).symm (g.toStarAlgEquiv.symm (ultraweakLinearEquiv P x)))))
      exact congrArg (fun y : N => (ultraweakLinearEquiv M).symm (f.toStarAlgEquiv.symm y))
        ((ultraweakLinearEquiv N).apply_symm_apply
          (g.toStarAlgEquiv.symm (ultraweakLinearEquiv P x))).symm
    rw [hfun]
    exact f.continuous_ultraweak_symm.comp g.continuous_ultraweak_symm

/-- **Forward value of composed normal equivalences.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence,
ultraweakly continuous in both directions. for a normal equivalence `g : N ≃ P` and `x ∈
M`, `f.trans g x=g(f(x))`. -/
@[simp]
theorem trans_apply (f : NormalStarAlgEquiv M N) (g : NormalStarAlgEquiv N P) (x : M) :
    f.trans g x = g (f x) :=
  rfl

/-- **Group of normal star automorphisms.** Let `H` be a complete complex Hilbert space and `M
⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. the
normal star automorphisms of `M` form a group with identity `id`, product
`(f*g)(x)=f(g(x))` and inverse the normal inverse map. -/
instance automorphismGroup : Group (NormalStarAlgEquiv M M) where
  one := refl M
  mul f g := g.trans f
  inv f := f.symm
  mul_assoc f g h := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    rfl
  one_mul f := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    rfl
  mul_one f := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    rfl
  inv_mul_cancel f := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    exact f.toStarAlgEquiv.symm_apply_apply x

/-- **Identity normal automorphism value.** Let `H` be a complete complex Hilbert space and `M
⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. for
`x ∈ M`, `(1 : NormalStarAlgEquiv M M)(x)=x`. -/
@[simp]
theorem one_apply (x : M) : (1 : NormalStarAlgEquiv M M) x = x :=
  rfl

/-- **Product of normal automorphisms is function composition.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `f,g` be normal complex star automorphisms of `M`. for `x ∈ M`,
`(f*g)(x)=f(g(x))`. -/
@[simp]
theorem mul_apply (f g : NormalStarAlgEquiv M M) (x : M) : (f * g) x = f (g x) :=
  rfl

/-- **Inverse normal automorphism value.** Let `H` be a complete complex Hilbert space and `M
⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. Let
`f,g` be normal complex star automorphisms of `M`. for `x ∈ M`, `f⁻¹(x)=f.symm x`. -/
@[simp]
theorem inv_apply (f : NormalStarAlgEquiv M M) (x : M) : f⁻¹ x = f.symm x :=
  rfl

/-- **Forgetful group map from normal to star automorphisms.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. `toStarAlgAutHom M` sends a normal automorphism to its underlying complex
star-algebra automorphism and preserves identity and composition. -/
def toStarAlgAutHom (M : VonNeumannAlgebra H) :
    NormalStarAlgEquiv M M →* (M ≃⋆ₐ[ℂ] M) where
  toFun := toStarAlgEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **Continuous linear pullback equivalence of normal functionals.** Let `M,N` be concrete
von Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
topologies are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra
equivalence, ultraweakly continuous in both directions. `f.predualEquiv : N_* ≃L[ℂ] M_*`
sends `φ` to `φ∘f`, with inverse `ψ ↦ ψ∘f⁻¹`. -/
def predualEquiv (f : NormalStarAlgEquiv M N) :
    normalFunctionalSpace N ≃L[ℂ] normalFunctionalSpace M where
  toLinearEquiv :=
    { toFun := f.toNormalStarAlgHom.predualPullback
      invFun := f.symm.toNormalStarAlgHom.predualPullback
      left_inv := by
        intro φ
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro x
        simp only [NormalStarAlgHom.predualPullback_apply, toNormalStarAlgHom_apply,
          apply_symm_apply]
      right_inv := by
        intro φ
        apply Subtype.ext
        apply ContinuousLinearMap.ext
        intro x
        simp only [NormalStarAlgHom.predualPullback_apply, toNormalStarAlgHom_apply,
          symm_apply_apply]
      map_add' := map_add f.toNormalStarAlgHom.predualPullback
      map_smul' := map_smul f.toNormalStarAlgHom.predualPullback }
  continuous_toFun := f.toNormalStarAlgHom.predualPullback.continuous
  continuous_invFun := f.symm.toNormalStarAlgHom.predualPullback.continuous

/-- **Evaluation of the predual equivalence.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M ≃ N` be a complex star-algebra equivalence, ultraweakly continuous
in both directions. for `φ ∈ N_*` and `x ∈ M`, `(f.predualEquiv φ)(x)=φ(f(x))`. -/
@[simp]
theorem predualEquiv_apply (f : NormalStarAlgEquiv M N) (φ : normalFunctionalSpace N) (x : M) :
    (f.predualEquiv φ : StrongDual ℂ M) x = (φ : StrongDual ℂ N) (f x) :=
  f.toNormalStarAlgHom.predualPullback_apply φ x

/-- **Covariant normal-automorphism action on the predual.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. `predualActionHom M` is the group homomorphism sending a normal automorphism `f` to
the continuous linear automorphism `φ ↦ φ∘f⁻¹` of `M_*`. -/
def predualActionHom (M : VonNeumannAlgebra H) :
    NormalStarAlgEquiv M M →*
      (normalFunctionalSpace M ≃L[ℂ] normalFunctionalSpace M) where
  toFun f := f.symm.predualEquiv
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext φ
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change (((1 : NormalStarAlgEquiv M M).symm).predualEquiv φ : StrongDual ℂ M) x =
      (φ : StrongDual ℂ M) x
    rw [predualEquiv_apply]
    rfl
  map_mul' f g := by
    apply ContinuousLinearEquiv.ext
    funext φ
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change ((f * g).symm.predualEquiv φ : StrongDual ℂ M) x =
      (f.symm.predualEquiv (g.symm.predualEquiv φ) : StrongDual ℂ M) x
    rw [predualEquiv_apply, predualEquiv_apply, predualEquiv_apply]
    change (φ : StrongDual ℂ M) ((g.toStarAlgEquiv.trans f.toStarAlgEquiv).symm x) =
      (φ : StrongDual ℂ M) (g.toStarAlgEquiv.symm (f.toStarAlgEquiv.symm x))
    rw [StarAlgEquiv.symm_trans_apply]

/-- **Inverse-automorphism formula for the predual action.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. Let `f,g` be normal complex star automorphisms of `M`. for `φ ∈ M_*` and `x ∈ M`,
`(predualActionHom M f φ)(x)=φ(f⁻¹(x))`. -/
@[simp]
theorem predualActionHom_apply (f : NormalStarAlgEquiv M M)
    (φ : normalFunctionalSpace M) (x : M) :
    (predualActionHom M f φ : StrongDual ℂ M) x = (φ : StrongDual ℂ M) (f.symm x) :=
  f.symm.predualEquiv_apply φ x

end NormalStarAlgEquiv

end

end VonNeumannAlgebra
