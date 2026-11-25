/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Chevalley–Eilenberg chain data

Exterior powers supply the degree objects. `ChainData` bundles square-zero
differentials, while a pure-wedge presentation specifies their values on
decomposable wedges. The canonical bracket formula places each bracket first;
in degree two its value is `-[x, y]`.

Compatibility with a Lie algebra map gives a chain map. These data also
support transport from complexes equipped with exterior-power coordinates.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Degree `n` of the trivial-coefficient Chevalley--Eilenberg chains. -/
abbrev chainObject (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⋀[R]^n L)

/-- The map on degree `n` exterior powers induced by a Lie algebra map. -/
def chainObjectMap
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (n : ℕ) : chainObject R L n ⟶ chainObject R L' n :=
  ModuleCat.ofHom (exteriorPower.map n f.toLinearMap)

@[simp]
theorem chainObjectMap_id (n : ℕ) :
    chainObjectMap R L (LieHom.id : L →ₗ⁅R⁆ L) n = 𝟙 _ := by
  change ModuleCat.ofHom (exteriorPower.map n LinearMap.id) = _
  rw [exteriorPower.map_id]
  rfl

@[simp]
theorem chainObjectMap_comp
    {L' L'' : Type v}
    [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
    (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') (n : ℕ) :
    chainObjectMap R L f n ≫ chainObjectMap R L' g n =
      chainObjectMap R L (g.comp f) n := by
  rw [chainObjectMap, chainObjectMap, chainObjectMap]
  rw [← ModuleCat.ofHom_comp, ← exteriorPower.map_comp]
  rfl

/-- Lawful differential data on the canonical exterior-power degree objects.
The CE pure-wedge formula is intentionally a separate property. -/
structure ChainData where
  /-- Differential from exterior degree `n+1` to exterior degree `n`. -/
  d : ∀ n : ℕ, (⋀[R]^(n + 1) L) →ₗ[R] (⋀[R]^n L)
  /-- Consecutive differentials compose to zero. -/
  d_comp_d : ∀ n : ℕ, (d n).comp (d (n + 1)) = 0

/-- A pure-wedge formula for a differential on exterior powers. -/
abbrev PureBoundary := ∀ n : ℕ, (Fin (n + 1) → L) → (⋀[R]^n L)

/-- The bracket part of the trivial-coefficient Chevalley--Eilenberg
differential, using zero-based indices. The bracket is placed at the front
of the remaining wedge; in degree two the boundary is `-[x,y]`. -/
noncomputable def bracketBoundary : PureBoundary R L
  | 0, _ => 0
  | n + 1, v =>
      ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
        ((-1 : R) ^ (i.val + j.val + 1)) •
          exteriorPower.ιMulti R (n + 1)
            (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
              (j.removeNth (i.castSucc.removeNth v)))

/-- CE differential data characterized on every decomposable wedge by a
chosen pure-wedge formula. -/
structure PresentedData (boundary : PureBoundary R L) extends ChainData R L where
  /-- The differential has the prescribed value on every pure wedge. -/
  d_apply_ιMulti : ∀ (n : ℕ) (v : Fin (n + 1) → L),
    d n (exteriorPower.ιMulti R (n + 1) v) = boundary n v

/-- A pure-wedge presentation determines every differential uniquely. -/
theorem PresentedData.d_eq
    {boundary : PureBoundary R L}
    (D E : PresentedData R L boundary) (n : ℕ) : D.d n = E.d n := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := n + 1) (M := L) (N := ⋀[R]^n L)
  apply AlternatingMap.ext
  intro v
  change D.d n (exteriorPower.ιMulti R (n + 1) v) =
    E.d n (exteriorPower.ιMulti R (n + 1) v)
  rw [D.d_apply_ιMulti, E.d_apply_ιMulti]

variable {R L} in
/-- The differential from exterior degree one to degree zero vanishes in
every model presented by the canonical bracket formula. -/
theorem PresentedData.d_zero
    (D : PresentedData R L (bracketBoundary R L)) : D.d 0 = 0 := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := 1) (M := L) (N := ⋀[R]^0 L)
  apply AlternatingMap.ext
  intro a
  change D.d 0 (exteriorPower.ιMulti R 1 a) = 0
  exact D.d_apply_ιMulti 0 a

namespace ChainData

/-- The nonnegative chain complex carried by CE differential data. -/
def complex (D : ChainData R L) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of
    (chainObject R L)
    (fun n => ModuleCat.ofHom (D.d n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, D.d_comp_d, ModuleCat.ofHom_zero])

@[simp]
theorem complex_X (D : ChainData R L) (n : ℕ) :
    D.complex.X n = chainObject R L n :=
  rfl

@[simp]
theorem complex_d_succ (D : ChainData R L) (n : ℕ) :
    D.complex.d (n + 1) n = ModuleCat.ofHom (D.d n) := by
  simp [complex, ChainComplex.of_d]

/-- Transport any nonnegative complex with identified exterior-power terms
to canonical CE chain data. -/
def ofComplex
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (e : ∀ n : ℕ, K.X n ≅ chainObject R L n) : ChainData R L where
  d n := (e n).hom.hom.comp
    ((K.d (n + 1) n).hom.comp (e (n + 1)).inv.hom)
  d_comp_d n := by
    have h :
        ((e (n + 1 + 1)).inv ≫ K.d (n + 1 + 1) (n + 1) ≫
            (e (n + 1)).hom) ≫
          ((e (n + 1)).inv ≫ K.d (n + 1) n ≫ (e n).hom) = 0 := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      simp
    exact congrArg ModuleCat.Hom.hom h

/-- Compatibility of a Lie algebra map with two supplied CE differentials. -/
structure Hom
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    (D : ChainData R L) (D' : ChainData R L')
    (f : L →ₗ⁅R⁆ L') : Prop where
  /-- The exterior-power maps commute with the differentials. -/
  comm : ∀ n : ℕ,
    (D'.d n).comp (exteriorPower.map (n + 1) f.toLinearMap) =
      (exteriorPower.map n f.toLinearMap).comp (D.d n)

/-- Naturality of two pure-wedge boundary formulas along a Lie algebra map. -/
def BoundaryNatural
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    (boundary : PureBoundary R L) (boundary' : PureBoundary R L')
    (f : L →ₗ⁅R⁆ L') : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) → L),
    exteriorPower.map n f.toLinearMap (boundary n v) =
      boundary' n (fun i => f (v i))

/-- The canonical bracket boundary is natural under Lie algebra maps. -/
theorem bracketBoundary_natural
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') :
    BoundaryNatural R L (bracketBoundary R L) (bracketBoundary R L') f := by
  intro n x
  cases n with
  | zero => simp [bracketBoundary]
  | succ n =>
      simp only [bracketBoundary, map_sum, map_smul,
        exteriorPower.map_apply_ιMulti, Function.comp_def]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hv :
          (fun k => f (Matrix.vecCons ⁅x i.castSucc, x j.succ⁆
            (j.removeNth (i.castSucc.removeNth x)) k)) =
            Matrix.vecCons ⁅f (x i.castSucc), f (x j.succ)⁆
              (j.removeNth (i.castSucc.removeNth fun i => f (x i))) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · exact f.map_lie _ _
        · rfl
      congr 2

/-- Naturality of the pure-wedge formulas induces compatibility of the
presented CE differentials. -/
theorem homOfBoundaryNatural
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    {boundary : PureBoundary R L} {boundary' : PureBoundary R L'}
    (D : PresentedData R L boundary) (D' : PresentedData R L' boundary')
    (f : L →ₗ⁅R⁆ L') (hf : BoundaryNatural R L boundary boundary' f) :
    Hom (R := R) (L := L) D.toChainData D'.toChainData f where
  comm n := by
    apply exteriorPower.linearMap_ext
      (R := R) (n := n + 1) (M := L) (N := ⋀[R]^n L')
    apply AlternatingMap.ext
    intro v
    change D'.d n
        (exteriorPower.map (n + 1) f.toLinearMap
          (exteriorPower.ιMulti R (n + 1) v)) =
      exteriorPower.map n f.toLinearMap
        (D.d n (exteriorPower.ιMulti R (n + 1) v))
    rw [exteriorPower.map_apply_ιMulti, D'.d_apply_ιMulti,
      D.d_apply_ιMulti, hf n v]
    rfl

/-- A compatible Lie algebra map induces a chain map. -/
def map
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    {D : ChainData R L} {D' : ChainData R L'}
    (f : L →ₗ⁅R⁆ L') (hf : Hom (R := R) (L := L) D D' f) :
    D.complex ⟶ D'.complex :=
  ChainComplex.ofHom
    (chainObjectMap R L f)
    (fun n => by
      rw [complex_d_succ, complex_d_succ]
      simp only [chainObjectMap]
      rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
      exact ModuleCat.hom_ext (hf.comm n))

@[simp]
theorem map_f
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    {D : ChainData R L} {D' : ChainData R L'}
    (f : L →ₗ⁅R⁆ L') (hf : Hom (R := R) (L := L) D D' f) (n : ℕ) :
    (map (R := R) (L := L) f hf).f n = chainObjectMap R L f n :=
  rfl

/-- The identity Lie map is compatible with any supplied CE differential. -/
theorem Hom.id (D : ChainData R L) :
    Hom (R := R) (L := L) D D (LieHom.id : L →ₗ⁅R⁆ L) where
  comm n := by
    change (D.d n).comp (exteriorPower.map (n + 1) LinearMap.id) =
      (exteriorPower.map n LinearMap.id).comp (D.d n)
    rw [exteriorPower.map_id, exteriorPower.map_id]
    simp

/-- Compatibility proofs compose with Lie algebra maps. -/
theorem Hom.comp
    {L' L'' : Type v}
    [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
    {D : ChainData R L} {D' : ChainData R L'} {D'' : ChainData R L''}
    {f : L →ₗ⁅R⁆ L'} {g : L' →ₗ⁅R⁆ L''}
    (F : Hom (R := R) (L := L) D D' f)
    (G : Hom (R := R) (L := L') D' D'' g) :
    Hom (R := R) (L := L) D D'' (g.comp f) where
  comm n := by
    rw [LieHom.toLinearMap_comp, exteriorPower.map_comp,
      exteriorPower.map_comp]
    simp only [← LinearMap.comp_assoc]
    rw [G.comm n]
    simp only [LinearMap.comp_assoc]
    rw [F.comm n]

@[simp]
theorem map_id (D : ChainData R L) :
    map (R := R) (L := L) (LieHom.id : L →ₗ⁅R⁆ L)
        (Hom.id (R := R) (L := L) D) =
      𝟙 D.complex := by
  apply HomologicalComplex.hom_ext
  intro n
  change chainObjectMap R L (LieHom.id : L →ₗ⁅R⁆ L) n =
    𝟙 (chainObject R L n)
  exact chainObjectMap_id R L n

@[simp]
theorem map_comp
    {L' L'' : Type v}
    [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
    {D : ChainData R L} {D' : ChainData R L'} {D'' : ChainData R L''}
    {f : L →ₗ⁅R⁆ L'} {g : L' →ₗ⁅R⁆ L''}
    (F : Hom (R := R) (L := L) D D' f)
    (G : Hom (R := R) (L := L') D' D'' g) :
    map (R := R) (L := L) f F ≫ map (R := R) (L := L') g G =
      map (R := R) (L := L) (g.comp f)
        (F.comp (R := R) (L := L) G) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, map_f, map_f, map_f,
    chainObjectMap_comp]

end ChainData

end ChevalleyEilenberg
