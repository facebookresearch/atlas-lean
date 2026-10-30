/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.PatchingDatum

@[expose] public section

/-- The level projection of a patching datum has the expected type, and its
surjectivity data is accessible. -/
example {𝒪 : Type} [CommRing 𝒪] {ℓ r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] (D : Algebra.PatchingDatum 𝒪 ℓ r R M)
    (n : ℕ) :
    Function.Surjective ((D.level n).π) :=
  (D.level n).π_surjective

noncomputable section

variable {𝒪 : Type} [CommRing 𝒪] {ℓ r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] (D : Algebra.PatchingDatum 𝒪 ℓ r R M)
    (n : ℕ)

-- The published instances must synthesize through the dependent level projection.
example : AddCommGroup (D.level n).N := inferInstance

example : Module (MvPowerSeries (Fin r) 𝒪) (D.level n).N := inferInstance

-- The projection is immediately usable by the standard semilinear map API.
example : (D.level n).N →ₛₗ[(D.level n).ψ.toRingHom] M :=
  (D.level n).π

example : (D.level n).N →+ M := (D.level n).π.toAddMonoidHom

example (f : MvPowerSeries (Fin r) 𝒪) (x : (D.level n).N) :
    (D.level n).π (f • x) = (D.level n).ψ f • (D.level n).π x :=
  (D.level n).π.map_smulₛₗ f x

example : LinearMap.ker (D.level n).π =
    (Ideal.span (Set.range fun i : Fin r => (D.level n).φ (MvPowerSeries.X i))) •
      (⊤ : Submodule (MvPowerSeries (Fin r) 𝒪) (D.level n).N) :=
  (D.level n).ker_π

-- The canonical kernel equality recovers the original pointwise condition.
example (x : (D.level n).N) : (D.level n).π x = 0 ↔
    x ∈ (Ideal.span (Set.range fun i : Fin r => (D.level n).φ (MvPowerSeries.X i))) •
      (⊤ : Submodule (MvPowerSeries (Fin r) 𝒪) (D.level n).N) := by
  rw [← LinearMap.mem_ker, (D.level n).ker_π]

-- The coefficient map's recorded surjectivity supplies the standard range API instance.
local instance : RingHomSurjective (D.level n).ψ.toRingHom :=
  ⟨(D.level n).ψ_surjective⟩

example : LinearMap.range (D.level n).π = ⊤ :=
  LinearMap.range_eq_top.mpr (D.level n).π_surjective

example {P : Type} [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) :
    (D.level n).N →ₛₗ[(D.level n).ψ.toRingHom] P :=
  f.comp (D.level n).π

example {P : Type} [AddCommGroup P] [Module R P] (f : M →ₗ[R] P)
    (x : (D.level n).N) :
    (f.comp (D.level n).π) x = f ((D.level n).π x) :=
  LinearMap.comp_apply f (D.level n).π x

end
