/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Wedderburn blocks give irreducible representations

Given a Wedderburn–Artin decomposition of the group algebra
`k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k` of a finite group `G`
over an algebraically closed field `k`, the representation obtained by
projecting onto the `i`-th matrix block and letting it act on
`Fin (d i) → k` is irreducible.

This is the `wedderburnIrrep_isIrreducible` claim of the v1
`CharacterTheory` development, whose proof there is left unproved. The proof
here is the standard one: the composite algebra map
`k[G] → Module.End k (Fin (d i) → k)` is surjective (its factors are an
algebra equivalence, evaluation at `i`, and the matrix-to-linear-map
equivalence), and `Fin (d i) → k` is simple as a module over its own
endomorphism ring, so it is simple as a module over `k[G]` along the
surjective map.

Source: `v1/Atlas/AlgebraNotes/code/Characters.lean` (definitions
`CharacterTheory.wedderburnIrrep` and theorem
`CharacterTheory.wedderburnIrrep_isIrreducible`). The v1 theorem
statement is ported verbatim; the only adaptation is factoring the
composite algebra map in `wedderburnIrrep` through the auxiliary
`wedderburnAlgHom`, so that the proof can refer to it directly. The
corresponding block-size / sum-of-squares consequence was ported
separately and does not depend on this result.
-/

@[expose] public section

namespace CharacterTheory

universe u

/-- The algebra map `k[G] → Module.End k (Fin (d i) → k)` underlying the
`i`-th Wedderburn block: the Wedderburn equivalence, evaluation at `i`,
and the matrix-to-linear-map equivalence. -/
noncomputable def wedderburnAlgHom (k : Type u) [Field k] [IsAlgClosed k]
    (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : k)]
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra k G ≃ₐ[k] Π j, Matrix (Fin (d j)) (Fin (d j)) k)
    (i : Fin n) :
    MonoidAlgebra k G →ₐ[k] Module.End k (Fin (d i) → k) :=
  (Matrix.toLinAlgEquiv' (R := k) (n := Fin (d i))).toAlgHom.comp
    ((Pi.evalAlgHom k _ i).comp e.toAlgHom)

/-- The representation of `G` obtained from the `i`-th block of a
Wedderburn–Artin decomposition of the group algebra: project onto the
`i`-th matrix algebra and let the matrix act on `Fin (d i) → k`. -/
noncomputable def wedderburnIrrep (k : Type u) [Field k] [IsAlgClosed k]
    (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : k)]
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra k G ≃ₐ[k] Π j, Matrix (Fin (d j)) (Fin (d j)) k)
    (i : Fin n) :
    Representation k G (Fin (d i) → k) :=
  (wedderburnAlgHom k G e i).toRingHom.toMonoidHom.comp (MonoidAlgebra.of k G)

/-- **Wedderburn blocks are irreducible.** The representation obtained
from the `i`-th block of a Wedderburn–Artin decomposition of `k[G]` is
irreducible, provided the block is nonzero. -/
theorem wedderburnIrrep_isIrreducible (k : Type u) [Field k] [IsAlgClosed k]
    (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : k)]
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra k G ≃ₐ[k] Π j, Matrix (Fin (d j)) (Fin (d j)) k)
    (i : Fin n) [NeZero (d i)] :
    (wedderburnIrrep k G e i).IsIrreducible := by
  classical
  -- The representation's algebra map is exactly `wedderburnAlgHom`: both
  -- are algebra maps out of the group algebra agreeing on the generators.
  have hΦ : Representation.asAlgebraHom (wedderburnIrrep k G e i) =
      wedderburnAlgHom k G e i := by
    apply MonoidAlgebra.algHom_ext'
    · ext g
      simp [wedderburnIrrep, wedderburnAlgHom]
    · ext
  -- `wedderburnAlgHom` is surjective: its factors are an algebra
  -- equivalence, evaluation at `i`, and the matrix-to-linear-map
  -- equivalence.
  have hΦsurj : Function.Surjective (wedderburnAlgHom k G e i) := by
    have heval : Function.Surjective
        (Pi.evalAlgHom k (fun j => Matrix (Fin (d j)) (Fin (d j)) k) i) := by
      intro x
      exact ⟨Function.update 0 i x, by simp⟩
    exact (Matrix.toLinAlgEquiv' (R := k) (n := Fin (d i))).bijective.2.comp
      (heval.comp e.bijective.2)
  have hnonempty : Nonempty (Fin (d i)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨?_, ?_⟩
  · show Nontrivial (Fin (d i) → k)
    infer_instance
  · intro x hx z
    -- View `x` in the underlying vector space.
    set xV : Fin (d i) → k :=
      (wedderburnIrrep k G e i).asModuleEquiv x with hxVdef
    have hxVne : xV ≠ 0 := hx
    -- `Fin (d i) → k` is simple as a module over its own endomorphism
    -- ring, so some endomorphism sends the nonzero vector `xV` to `z`.
    have hEnd : Function.Surjective
        (LinearMap.toSpanSingleton (Module.End k (Fin (d i) → k)) _ xV) :=
      (isSimpleModule_iff_toSpanSingleton_surjective.mp inferInstance).2 xV hxVne
    obtain ⟨T, hT⟩ := hEnd z
    -- Pull the endomorphism back along the surjective `wedderburnAlgHom`.
    obtain ⟨a, ha⟩ := hΦsurj T
    refine ⟨a, ?_⟩
    rw [LinearMap.toSpanSingleton_apply]
    -- The `k[G]`-action on the representation space is through
    -- `wedderburnAlgHom`.
    have h := Representation.asModuleEquiv_map_smul (wedderburnIrrep k G e i) a x
    rw [hΦ] at h
    rw [ha] at h
    exact h.trans hT

end CharacterTheory
