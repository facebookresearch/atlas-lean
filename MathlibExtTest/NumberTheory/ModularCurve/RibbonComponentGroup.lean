/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurve.RibbonComponentGroup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open ModularCurve CerednikDrinfeld

/-- A concrete degeneracy datum: two edges over one vertex, of
width `1`. -/
private def bananaData : DegeneracyData (Fin 2) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  w := fun _ => 1

/-- The ribbon kernel of the banana datum sits in the character
lattice. -/
example : ribbonKernel bananaData ≤ characterLattice (Fin 2) :=
  ribbonKernel_le_characterLattice bananaData

/-- Pushforward along the constant vertex map preserves degrees. -/
example (x : Fin 2 → ℤ) :
    degreeOn (Fin 1) (pushforward bananaData.a x) = degreeOn (Fin 2) x :=
  degreeOn_pushforward _ x

/-- The ribbon Gram pairing on the banana datum. -/
example (x y : ribbonKernel bananaData) :
    ribbonGram bananaData x y =
      ∑ e : Fin 2, (bananaData.w e : ℤ) * (x.1 e * y.1 e) :=
  ribbonGram_apply _ _ _

/-- The projection to the ribbon component group of the banana
datum. -/
example : Module.Dual ℤ ↥(ribbonKernel bananaData) →ₗ[ℤ]
    ribbonComponentGroup bananaData :=
  ribbonComponentGroupProj bananaData

/-- Membership in the ribbon kernel of the banana datum, unfolded. -/
example (x : Fin 2 → ℤ) :
    x ∈ ribbonKernel bananaData ↔
      ∀ i, jointDelta bananaData i x = 0 :=
  mem_ribbonKernel

/-! ### Pushforwards and ribbon kernels of concrete data -/

/-- Pushforward along a vertex map adds up the edge values over each
fibre. -/
private theorem pushforward_apply {E V : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (x : E → ℤ) (v : V) :
    pushforward f x v = ∑ e, if f e = v then x e else 0 := by
  simp [pushforward, degeneracyMatrix, Matrix.mulVec, dotProduct]

/-- On the banana datum, both degeneracy pushforwards add up the two
edge values at the single vertex. -/
example (x : Fin 2 → ℤ) (i : Fin 2) :
    jointDelta bananaData i x 0 = x 0 + x 1 := by
  fin_cases i <;> simp [jointDelta, pushforward_apply, bananaData, Fin.sum_univ_two]

/-- The banana kernel: the two edge values cancel. -/
private theorem mem_ribbonKernel_bananaData (x : Fin 2 → ℤ) :
    x ∈ ribbonKernel bananaData ↔ x 0 + x 1 = 0 := by
  simp [mem_ribbonKernel, Fin.forall_fin_two, jointDelta, funext_iff, pushforward_apply,
    bananaData, Fin.sum_univ_two]

example : (![1, -1] : Fin 2 → ℤ) ∈ ribbonKernel bananaData := by
  simp [mem_ribbonKernel_bananaData]

example : (![1, 0] : Fin 2 → ℤ) ∉ ribbonKernel bananaData := by
  simp [mem_ribbonKernel_bananaData]

/-- A nontrivial degeneracy datum: the complete bipartite graph `K₂,₂`,
a cycle of four edges, with edge `e` joining `a e` in the first vertex
copy to `b e` in the second, and widths `1, 2, 2, 1`. -/
private def squareData : DegeneracyData (Fin 4) (Fin 2) where
  a := ![0, 0, 1, 1]
  b := ![0, 1, 0, 1]
  w := ![1, 2, 2, 1]

/-- The first degeneracy pushforward of the square datum adds up edges
`0, 1` at vertex `0` and edges `2, 3` at vertex `1`. -/
example : jointDelta squareData 0 ![1, 2, 3, 4] = ![3, 7] := by
  funext v
  fin_cases v <;> simp [jointDelta, pushforward_apply, squareData, Fin.sum_univ_four]

/-- The second degeneracy pushforward adds up edges `0, 2` at vertex `0`
and edges `1, 3` at vertex `1`. -/
example : jointDelta squareData 1 ![1, 2, 3, 4] = ![4, 6] := by
  funext v
  fin_cases v <;> simp [jointDelta, pushforward_apply, squareData, Fin.sum_univ_four]

/-- The square kernel is spanned by the alternating cycle
`(1, -1, -1, 1)`. -/
private theorem mem_ribbonKernel_squareData (x : Fin 4 → ℤ) :
    x ∈ ribbonKernel squareData ↔ x 1 = -x 0 ∧ x 2 = -x 0 ∧ x 3 = x 0 := by
  simp only [mem_ribbonKernel, Fin.forall_fin_two, funext_iff, jointDelta]
  simp [pushforward_apply, squareData, Fin.sum_univ_four]
  omega

/-- A function killed by the first pushforward only is not in the
ribbon kernel. -/
example : pushforward squareData.a ![1, -1, 0, 0] = 0 ∧
    (![1, -1, 0, 0] : Fin 4 → ℤ) ∉ ribbonKernel squareData := by
  refine ⟨?_, by simp [mem_ribbonKernel_squareData]⟩
  funext v
  fin_cases v <;> simp [pushforward_apply, squareData, Fin.sum_univ_four]

/-- A function killed by the second pushforward only is not in the
ribbon kernel. -/
example : pushforward squareData.b ![1, 0, -1, 0] = 0 ∧
    (![1, 0, -1, 0] : Fin 4 → ℤ) ∉ ribbonKernel squareData := by
  refine ⟨?_, by simp [mem_ribbonKernel_squareData]⟩
  funext v
  fin_cases v <;> simp [pushforward_apply, squareData, Fin.sum_univ_four]

/-! ### The component group of the square datum -/

/-- The alternating cycle, as an element of the square kernel. -/
private def cycleSq : ribbonKernel squareData :=
  ⟨![1, -1, -1, 1], by simp [mem_ribbonKernel_squareData]⟩

/-- The value at edge `0`, a functional on the square kernel. -/
private def evalSq : Module.Dual ℤ (ribbonKernel squareData) :=
  (LinearMap.proj 0).comp (ribbonKernel squareData).subtype

/-- The ribbon Gram pairing on the square kernel is `6` times the
product of the edge-`0` values: the widths add up along the cycle. -/
private theorem ribbonGram_squareData (x y : ribbonKernel squareData) :
    ribbonGram squareData x y = 6 * (x.1 0 * y.1 0) := by
  obtain ⟨hx1, hx2, hx3⟩ := (mem_ribbonKernel_squareData x.1).1 x.2
  obtain ⟨hy1, hy2, hy3⟩ := (mem_ribbonKernel_squareData y.1).1 y.2
  rw [ribbonGram_apply, Fin.sum_univ_four, hx1, hx2, hx3, hy1, hy2, hy3]
  simp [squareData]
  ring

example : ribbonGram squareData cycleSq cycleSq = 6 := by
  rw [ribbonGram_squareData]
  simp [cycleSq]

/-- The class of `n` times the edge-`0` functional vanishes in the
component group exactly when `6` divides `n`: the component group of
the square datum contains a cyclic subgroup of order `6`. -/
private theorem ribbonComponentGroupProj_smul_evalSq_eq_zero_iff (n : ℤ) :
    ribbonComponentGroupProj squareData (n • evalSq) = 0 ↔ 6 ∣ n := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    have h := LinearMap.congr_fun hy cycleSq
    rw [ribbonGram_squareData] at h
    simp [evalSq, cycleSq] at h
    exact ⟨y.1 0, by omega⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k • cycleSq, LinearMap.ext fun x => ?_⟩
    rw [ribbonGram_squareData]
    simp [evalSq, cycleSq]
    ring

example : ribbonComponentGroupProj squareData evalSq ≠ 0 := by
  simpa using (ribbonComponentGroupProj_smul_evalSq_eq_zero_iff 1).not.2 (by decide)

example : ribbonComponentGroupProj squareData ((6 : ℤ) • evalSq) = 0 :=
  (ribbonComponentGroupProj_smul_evalSq_eq_zero_iff 6).2 dvd_rfl

/-! ### A scalar Hecke package -/

/-- A scalar matrix acts on functions by scalar multiplication. -/
private theorem smul_one_mulVecLin {E : Type*} [Fintype E] [DecidableEq E] (c : ℤ)
    (x : E → ℤ) : (c • 1 : Matrix E E ℤ).mulVecLin x = c • x := by
  rw [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The eigenvalue `ℓ + 1` of the scalar Hecke operator `T ℓ`. -/
private def heckeScalar (ℓ : Nat.Primes) : ℤ := (ℓ : ℕ) + 1

/-- The scalar Hecke package: `T ℓ` multiplies edge and vertex functions
by `ℓ + 1`. -/
private def scalarHecke {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V]
    [DecidableEq V] (D : DegeneracyData E V) : HeckeData D where
  T ℓ := heckeScalar ℓ • 1
  Tv ℓ := heckeScalar ℓ • 1
  comm _ _ := (Commute.one_left _).smul_left _
  commv _ _ := (Commute.one_left _).smul_left _
  S := ∅
  good_equivariant _ _ _ _ := by rw [smul_one_mulVecLin, smul_one_mulVecLin, map_smul]
  kernel_stable _ _ hx i := by rw [smul_one_mulVecLin, map_smul, hx i, smul_zero]

/-- The Hecke endomorphism of the ribbon kernel induced by the scalar
package is multiplication by `ℓ + 1`. -/
private theorem heckeKernelMap_scalarHecke {E V : Type*} [Fintype E] [DecidableEq E]
    [Fintype V] [DecidableEq V] (D : DegeneracyData E V) (ℓ : Nat.Primes)
    (x : ribbonKernel D) :
    heckeKernelMap (scalarHecke D) ℓ x = heckeScalar ℓ • x :=
  Subtype.ext (smul_one_mulVecLin _ x.1)

/-- The edge matrices of the scalar package act by `ℓ + 1`. -/
private theorem scalarHecke_T_mulVecLin {E V : Type*} [Fintype E] [DecidableEq E]
    [Fintype V] [DecidableEq V] (D : DegeneracyData E V) (ℓ : Nat.Primes) (x : E → ℤ) :
    ((scalarHecke D).T ℓ).mulVecLin x = heckeScalar ℓ • x :=
  smul_one_mulVecLin _ x

/-- The prime `2`. -/
private def prime2 : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The prime `5`. -/
private def prime5 : Nat.Primes := ⟨5, Nat.prime_five⟩

/-- `T 2` multiplies the alternating cycle by `3`. -/
example : heckeKernelMap (scalarHecke squareData) prime2 cycleSq = (3 : ℤ) • cycleSq :=
  heckeKernelMap_scalarHecke _ _ _

/-- The scalar Hecke endomorphism is self-adjoint for the ribbon Gram
pairing. -/
private theorem scalarHecke_adjoint {E V : Type*} [Fintype E] [DecidableEq E]
    [Fintype V] [DecidableEq V] (D : DegeneracyData E V) (ℓ : Nat.Primes)
    (x y : ribbonKernel D) :
    ribbonGram D (heckeKernelMap (scalarHecke D) ℓ x) y =
      ribbonGram D x (heckeKernelMap (scalarHecke D) ℓ y) := by
  rw [heckeKernelMap_scalarHecke, heckeKernelMap_scalarHecke, map_smul, map_smul,
    LinearMap.smul_apply]

/-- The endomorphism of the component group induced by the scalar
Hecke package is multiplication by `ℓ + 1` on classes of functionals. -/
private theorem ribbonComponentGroupMap_scalarHecke {E V : Type*} [Fintype E]
    [DecidableEq E] [Fintype V] [DecidableEq V] (D : DegeneracyData E V)
    (ℓ : Nat.Primes) (f : Module.Dual ℤ (ribbonKernel D)) :
    ribbonComponentGroupMap D (heckeKernelMap (scalarHecke D) ℓ)
        (heckeKernelMap (scalarHecke D) ℓ) (scalarHecke_adjoint D ℓ)
        (ribbonComponentGroupProj D f) =
      ribbonComponentGroupProj D (heckeScalar ℓ • f) := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  ext x
  simp [heckeKernelMap_scalarHecke]

/-- `T 2` acts on the component group of the square datum by `3`, so it
moves the class of the edge-`0` functional to a nonzero class. -/
example : ribbonComponentGroupMap squareData
    (heckeKernelMap (scalarHecke squareData) prime2)
    (heckeKernelMap (scalarHecke squareData) prime2)
    (scalarHecke_adjoint squareData _) (ribbonComponentGroupProj squareData evalSq) ≠ 0 := by
  rw [ribbonComponentGroupMap_scalarHecke, Ne, show heckeScalar prime2 = 3 from rfl,
    ribbonComponentGroupProj_smul_evalSq_eq_zero_iff]
  decide

/-- `T 5` acts on the component group of the square datum by `6`, which
kills the class of the edge-`0` functional. -/
example : ribbonComponentGroupMap squareData
    (heckeKernelMap (scalarHecke squareData) prime5)
    (heckeKernelMap (scalarHecke squareData) prime5)
    (scalarHecke_adjoint squareData _) (ribbonComponentGroupProj squareData evalSq) = 0 := by
  rw [ribbonComponentGroupMap_scalarHecke, show heckeScalar prime5 = 6 from rfl,
    ribbonComponentGroupProj_smul_evalSq_eq_zero_iff]

/-! ### Hecke data alone does not act on the component group -/

/-- Three edges of width `1` over one vertex. -/
private def tripleData : DegeneracyData (Fin 3) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  w := fun _ => 1

/-- Both pushforwards of the triple datum add up the three edge values. -/
private theorem jointDelta_tripleData (i : Fin 2) (x : Fin 3 → ℤ) :
    jointDelta tripleData i x = fun _ => x 0 + x 1 + x 2 := by
  funext v
  fin_cases i <;> fin_cases v <;>
    simp [jointDelta, pushforward_apply, tripleData, Fin.sum_univ_three]

/-- The triple kernel: the three edge values add up to zero. -/
private theorem mem_ribbonKernel_tripleData (x : Fin 3 → ℤ) :
    x ∈ ribbonKernel tripleData ↔ x 0 + x 1 + x 2 = 0 := by
  simp [mem_ribbonKernel, jointDelta_tripleData, funext_iff]

/-- The shear `x ↦ x + x 0 • (0, 1, -1)` on the edges. -/
private def shearMat : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 1, 1, 0; -1, 0, 1]

private theorem shearMat_mulVecLin (x : Fin 3 → ℤ) :
    shearMat.mulVecLin x = ![x 0, x 0 + x 1, -x 0 + x 2] := by
  funext i
  fin_cases i <;> simp [shearMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The shear preserves both pushforwards of the triple datum. -/
private theorem jointDelta_tripleData_shear (i : Fin 2) (x : Fin 3 → ℤ) :
    jointDelta tripleData i (shearMat.mulVecLin x) = jointDelta tripleData i x := by
  rw [jointDelta_tripleData, jointDelta_tripleData, shearMat_mulVecLin]
  funext _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- The shear, with identity vertex matrices and no bad prime, satisfies
every field of `HeckeData`. -/
private def shearHecke : HeckeData tripleData where
  T _ := shearMat
  Tv _ := 1
  comm _ _ := Commute.refl _
  commv _ _ := Commute.refl _
  S := ∅
  good_equivariant _ _ _ _ := by
    rw [jointDelta_tripleData_shear, Matrix.mulVecLin_one, LinearMap.id_apply]
  kernel_stable _ _ hx i := by rw [jointDelta_tripleData_shear, hx i]

/-- The Hecke endomorphism of the shear package on the triple kernel. -/
private theorem coe_heckeKernelMap_shearHecke (ℓ : Nat.Primes) (x : ribbonKernel tripleData) :
    (heckeKernelMap shearHecke ℓ x : Fin 3 → ℤ) = ![x.1 0, x.1 0 + x.1 1, -x.1 0 + x.1 2] :=
  shearMat_mulVecLin x.1

/-- The kernel element `(1, 0, -1)`. -/
private def uTri : ribbonKernel tripleData :=
  ⟨![1, 0, -1], by simp [mem_ribbonKernel_tripleData]⟩

/-- The kernel element `(0, 1, -1)`. -/
private def vTri : ribbonKernel tripleData :=
  ⟨![0, 1, -1], by simp [mem_ribbonKernel_tripleData]⟩

/-- The ribbon Gram pairing of the triple datum is the dot product. -/
private theorem ribbonGram_tripleData (x y : ribbonKernel tripleData) :
    ribbonGram tripleData x y = x.1 0 * y.1 0 + x.1 1 * y.1 1 + x.1 2 * y.1 2 := by
  rw [ribbonGram_apply, Fin.sum_univ_three]
  simp [tripleData]

/-- `HeckeData` alone does not act on the ribbon component group: the
shear package satisfies every field of `HeckeData`, but its Hecke
endomorphism of the triple kernel has no adjoint for the ribbon Gram
pairing, so `ribbonComponentGroupMap` does not apply to it. The dual of
the shear sends the Gram image of `(1, 0, -1)`, with values `(2, 1)` on
`(1, 0, -1), (0, 1, -1)`, to the functional with values `(3, 1)`, which
is not in the Gram image. -/
example (ℓ : Nat.Primes) :
    ¬ ∃ A : ribbonKernel tripleData →ₗ[ℤ] ribbonKernel tripleData,
      ∀ x y, ribbonGram tripleData (A x) y =
        ribbonGram tripleData x (heckeKernelMap shearHecke ℓ y) := by
  rintro ⟨A, hadj⟩
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 (ribbonGram_range_map_dualMap_le tripleData A _ hadj
    (Submodule.mem_map_of_mem (LinearMap.mem_range_self (ribbonGram tripleData) uTri)))
  have hu := LinearMap.congr_fun hy uTri
  have hv := LinearMap.congr_fun hy vTri
  have hy0 := (mem_ribbonKernel_tripleData y.1).1 y.2
  simp only [LinearMap.dualMap_apply, ribbonGram_tripleData, coe_heckeKernelMap_shearHecke] at hu hv
  simp [uTri, vTri] at hu hv
  omega

/-! ### Matchings -/

/-- The vertex swap of `K₂,₂`, which exchanges edges `0 ↔ 3` and
`1 ↔ 2`, is a matching of the scalar Hecke package with itself: it
preserves both degeneracy maps and the widths. -/
example : Matching (scalarHecke squareData) (scalarHecke squareData) where
  eE := (Equiv.swap 0 3).trans (Equiv.swap 1 2)
  eV := Equiv.swap 0 1
  map_a := by decide
  map_b := by decide
  map_w := by decide
  bad := ∅
  away_intertwine _ _ x := by
    rw [scalarHecke_T_mulVecLin, scalarHecke_T_mulVecLin]
    rfl
  bad_kernel_intertwine _ h := absurd h (Finset.notMem_empty _)

/-- Swapping edges `0` and `1` while fixing the vertices respects the
first degeneracy map but not the second, so it is not a matching. -/
example : ¬ ∃ M : Matching (scalarHecke squareData) (scalarHecke squareData),
    M.eE = Equiv.swap 0 1 ∧ M.eV = Equiv.refl _ := by
  rintro ⟨M, hE, hV⟩
  have h := M.map_b 0
  rw [hE, hV] at h
  revert h
  decide

/-- The all-ones matrix on the edges of the square datum. -/
private def onesSq : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun _ _ => 1

/-- The all-ones matrix kills the ribbon kernel, which lies in the
character lattice. -/
private theorem onesSq_mulVecLin_eq_zero {x : Fin 4 → ℤ}
    (hx : x ∈ ribbonKernel squareData) : onesSq.mulVecLin x = 0 := by
  have h := mem_characterLattice.1 (ribbonKernel_le_characterLattice squareData hx)
  funext e
  simp [onesSq, Matrix.mulVec, dotProduct, h]

/-- A matrix `c • 1 + d • onesSq` acts by `x ↦ c • x + d • onesSq x`. -/
private theorem smul_one_add_smul_onesSq_mulVecLin (c d : ℤ) (x : Fin 4 → ℤ) :
    (c • 1 + d • onesSq).mulVecLin x = c • x + d • onesSq.mulVecLin x := by
  rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVecLin_apply]

/-- A Hecke package on the square datum that differs from the scalar one
at the bad prime `2` only: there `T 2` also adds the all-ones matrix,
which kills the ribbon kernel but does not commute with the degeneracy
pushforwards. -/
private def twistedHecke : HeckeData squareData where
  T ℓ := heckeScalar ℓ • 1 + (if ℓ = prime2 then 1 else 0 : ℤ) • onesSq
  Tv ℓ := heckeScalar ℓ • 1
  comm _ _ := ((Commute.one_left _).smul_left _).add_left
    ((((Commute.one_right _).smul_right _).add_right ((Commute.refl _).smul_right _)).smul_left _)
  commv _ _ := (Commute.one_left _).smul_left _
  S := {prime2}
  good_equivariant _ hℓ _ _ := by
    rw [ite_eq_right (Finset.notMem_singleton.1 hℓ), zero_smul, add_zero, smul_one_mulVecLin,
      smul_one_mulVecLin, map_smul]
  kernel_stable _ _ hx i := by
    rw [smul_one_add_smul_onesSq_mulVecLin, onesSq_mulVecLin_eq_zero (mem_ribbonKernel.2 hx),
      smul_zero, add_zero, map_smul, hx i, smul_zero]

/-- The edge matrices of the twisted package. -/
private theorem twistedHecke_T_mulVecLin (ℓ : Nat.Primes) (x : Fin 4 → ℤ) :
    (twistedHecke.T ℓ).mulVecLin x =
      heckeScalar ℓ • x + (if ℓ = prime2 then 1 else 0 : ℤ) • onesSq.mulVecLin x :=
  smul_one_add_smul_onesSq_mulVecLin _ _ x

/-- The identity is a matching of the scalar and the twisted packages
once the prime `2` is declared bad: there the two packages agree on the
ribbon kernel only. -/
example : Matching (scalarHecke squareData) twistedHecke where
  eE := Equiv.refl _
  eV := Equiv.refl _
  map_a _ := rfl
  map_b _ := rfl
  map_w _ := rfl
  bad := {prime2}
  away_intertwine _ hℓ x := by
    rw [twistedHecke_T_mulVecLin, scalarHecke_T_mulVecLin,
      ite_eq_right (Finset.notMem_singleton.1 hℓ), zero_smul, add_zero]
    rfl
  bad_kernel_intertwine _ _ x hx := by
    simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id]
    rw [twistedHecke_T_mulVecLin, scalarHecke_T_mulVecLin, onesSq_mulVecLin_eq_zero hx,
      smul_zero, add_zero]

/-- No matching of the scalar and the twisted packages has an empty bad
set: at `2` they differ on the constant function `1`. -/
example : ¬ ∃ M : Matching (scalarHecke squareData) twistedHecke, M.bad = ∅ := by
  rintro ⟨M, hM⟩
  have h := congrFun (M.away_intertwine prime2 (by simp [hM]) fun _ => 1) 0
  revert h
  simp [twistedHecke, scalarHecke, onesSq, Matrix.mulVec, dotProduct]

/-! ### Matchings compare edge Hecke matrices only -/

/-- One edge whose two ends are the vertex `0` of two vertices. -/
private def edgeData : DegeneracyData (Fin 1) (Fin 2) where
  a := fun _ => 0
  b := fun _ => 0
  w := fun _ => 1

/-- Both pushforwards of `edgeData` put the edge value at the vertex `0`. -/
private theorem jointDelta_edgeData (i : Fin 2) (x : Fin 1 → ℤ) :
    jointDelta edgeData i x = ![x 0, 0] := by
  funext v
  fin_cases i <;> fin_cases v <;> simp [jointDelta, pushforward_apply, edgeData]

/-- A package on `edgeData` with identity edge matrices and a vertex matrix `Tv` that fixes the
functions supported at the vertex `0`. -/
private def edgeHecke (Tv : Matrix (Fin 2) (Fin 2) ℤ)
    (hTv : ∀ c : ℤ, Tv.mulVecLin ![c, 0] = ![c, 0]) : HeckeData edgeData where
  T _ := 1
  Tv _ := Tv
  comm _ _ := Commute.refl _
  commv _ _ := Commute.refl _
  S := ∅
  good_equivariant _ _ i x := by
    rw [Matrix.mulVecLin_one, LinearMap.id_apply, jointDelta_edgeData, hTv]
  kernel_stable _ x hx i := by
    rw [Matrix.mulVecLin_one, LinearMap.id_apply]
    exact hx i

/-- The package on `edgeData` with the identity vertex matrix. -/
private def edgeHeckeOne : HeckeData edgeData :=
  edgeHecke 1 fun c => by rw [Matrix.mulVecLin_one, LinearMap.id_apply]

/-- The package on `edgeData` with the vertex matrix `diag(1, 2)`. -/
private def edgeHeckeDiag : HeckeData edgeData :=
  edgeHecke !![1, 0; 0, 2] fun c => by
    funext v
    fin_cases v <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The identity relabelling, as a matching of the packages on `edgeData` with vertex matrices
`1` and `diag(1, 2)`. -/
private def edgeMatching : Matching edgeHeckeOne edgeHeckeDiag where
  eE := Equiv.refl _
  eV := Equiv.refl _
  map_a _ := rfl
  map_b _ := rfl
  map_w _ := rfl
  bad := ∅
  away_intertwine _ _ _ := rfl
  bad_kernel_intertwine _ h := absurd h (Finset.notMem_empty _)

/-- A matching compares the edge Hecke matrices only: the packages with vertex matrices `1` and
`diag(1, 2)` match, although their vertex matrices differ. -/
example : ∃ _ : Matching edgeHeckeOne edgeHeckeDiag,
    edgeHeckeOne.Tv prime2 ≠ edgeHeckeDiag.Tv prime2 := by
  refine ⟨edgeMatching, fun h => ?_⟩
  have h11 := congrFun (congrFun h 1) 1
  simp [edgeHeckeOne, edgeHeckeDiag, edgeHecke] at h11

/-- The identity relabelling, as a matching of the scalar package on the square datum with
itself, with the bad set `{5}`. -/
private def squareMatchingBad5 : Matching (scalarHecke squareData) (scalarHecke squareData) where
  eE := Equiv.refl _
  eV := Equiv.refl _
  map_a _ := rfl
  map_b _ := rfl
  map_w _ := rfl
  bad := {prime5}
  away_intertwine _ _ _ := rfl
  bad_kernel_intertwine _ _ _ _ := rfl

/-- The bad set of a matching is independent of the bad sets of the two packages: the scalar
package has no bad prime, and it matches itself with the bad set `{5}`. -/
example : ∃ M : Matching (scalarHecke squareData) (scalarHecke squareData),
    M.bad = {prime5} ∧ (scalarHecke squareData).S = ∅ :=
  ⟨squareMatchingBad5, rfl, rfl⟩
