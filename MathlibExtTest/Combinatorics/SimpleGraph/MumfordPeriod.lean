/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.MumfordPeriod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

open Mumford CerednikDrinfeld CerednikDrinfeld.Mumford

namespace MumfordPeriodTest

/-- Nontrivial instance: one edge with distinct ends and width `2`. The
zero chain lies in the ribbon kernel, the Gram pairing is symmetric on it,
and the period datum built from the zero pairing with the zero valuation
satisfies its defining equations. -/
example : True := by
  let D : DegeneracyData (Fin 1) (Fin 2) :=
    { a := fun _ => 0, b := fun _ => 1, w := fun _ => 2 }
  have h0 : (0 : Fin 1 → ℤ) ∈ ribbonKernel D := by
    rw [mem_ribbonKernel]
    intro i
    simp [jointDelta, pushforward]
  let P : PeriodDatum D ℚ ℚ (0 : Additive ℚˣ →+ ℤ) :=
    { Q := 0
      Q_symm := fun x y => rfl
      ord_Q := fun x y => by
        have hx : x.1 0 = 0 := by
          have h := mem_ribbonKernel.mp x.2 0
          have hDa : D.a 0 = 0 := rfl
          simpa [jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
            dotProduct, Fin.sum_univ_one, hDa] using congrFun h 0
        simp [ribbonGram_apply, hx] }
  have hsymm : ∀ x y : ribbonKernel D, P.Q x y = P.Q y x := P.Q_symm
  trivial

/-- Two parallel edges from `0` to `1`, with widths `1` and `2`. -/
private def twoEdges : DegeneracyData (Fin 2) (Fin 2) where
  a _ := 0
  b _ := 1
  w := ![1, 2]

/-- The difference of the two edges lies in the ribbon kernel. -/
private theorem diff_mem_ribbonKernel :
    (![1, -1] : Fin 2 → ℤ) ∈ ribbonKernel twoEdges := by
  rw [mem_ribbonKernel]
  intro i
  ext v
  fin_cases i <;> fin_cases v <;>
    simp [twoEdges, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The difference of the two edges, as an element of the ribbon kernel. -/
private def diff : ribbonKernel twoEdges := ⟨_, diff_mem_ribbonKernel⟩

/-- The `2`-adic valuation on the units of `ℚ`. -/
private noncomputable def ord₂ : Additive ℚˣ →+ ℤ :=
  AddMonoidHom.mk' (fun u => padicValRat 2 ((Additive.toMul u : ℚˣ) : ℚ))
    fun u v => by
      simp [padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]

/-- The unit `2` of `ℚ`. -/
private def two : ℚˣ := Units.mk0 2 two_ne_zero

private theorem ord₂_two : ord₂ (Additive.ofMul two) = 1 := by
  show padicValRat 2 ((two : ℚˣ) : ℚ) = 1
  rw [two, Units.val_mk0]
  exact_mod_cast padicValRat.self (p := 2) one_lt_two

/-- The period datum `Q x y = 2 ^ ⟨x, y⟩` on the two parallel edges, for the
`2`-adic valuation. -/
private noncomputable def twoEdgesPeriod : PeriodDatum twoEdges ℚ ℚ ord₂ where
  Q := (ribbonGram twoEdges).compr₂
    (LinearMap.toSpanSingleton ℤ (Additive ℚˣ) (Additive.ofMul two))
  Q_symm x y := by
    simp only [LinearMap.compr₂_apply, ribbonGram_apply]
    congr 1
    exact Finset.sum_congr rfl fun e _ => by ring
  ord_Q x y := by
    rw [LinearMap.compr₂_apply, LinearMap.toSpanSingleton_apply, map_zsmul,
      ord₂_two, smul_eq_mul, mul_one]

/-- A period datum with a nonzero Gram value. On two parallel edges of widths
`1` and `2`, the difference of the edges lies in the ribbon kernel, its Gram
value is `1 + 2 = 3`, and the valuation of its period is `3`. -/
example : ribbonGram twoEdges diff diff = 3 ∧
    ord₂ (twoEdgesPeriod.Q diff diff) = 3 := by
  have h : ribbonGram twoEdges diff diff = 3 := by
    rw [ribbonGram_apply, Fin.sum_univ_two]
    norm_num [diff, twoEdges]
  exact ⟨h, (twoEdgesPeriod.ord_Q diff diff).trans h⟩

/-- `-v₂`, the negative of the `2`-adic valuation on the units of `ℚ`. -/
private noncomputable def negOrd₂ : Additive ℚˣ →+ ℤ := -ord₂

/-- The unit `1/2` of `ℚ`. -/
private def half : ℚˣ := Units.mk0 (1 / 2) (by norm_num)

private theorem ord₂_half : ord₂ (Additive.ofMul half) = -1 := by
  show padicValRat 2 ((half : ℚˣ) : ℚ) = -1
  rw [half, Units.val_mk0, one_div, padicValRat.inv]
  exact_mod_cast congrArg Neg.neg (padicValRat.self (p := 2) one_lt_two)

/-- The period datum `Q x y = (1/2) ^ ⟨x, y⟩` on the two parallel edges, for
`ord = -v₂`. -/
private noncomputable def negPeriod : PeriodDatum twoEdges ℚ ℚ negOrd₂ where
  Q := (ribbonGram twoEdges).compr₂
    (LinearMap.toSpanSingleton ℤ (Additive ℚˣ) (Additive.ofMul half))
  Q_symm x y := by
    simp only [LinearMap.compr₂_apply, ribbonGram_apply]
    congr 1
    exact Finset.sum_congr rfl fun e _ => by ring
  ord_Q x y := by
    rw [LinearMap.compr₂_apply, LinearMap.toSpanSingleton_apply, map_zsmul,
      negOrd₂, AddMonoidHom.neg_apply, ord₂_half, smul_eq_mul]
    ring

/-- `ord` need not be a valuation. `-v₂` violates the valuation inequality at
`2 = 1 + 1`, yet `Q x y = (1/2) ^ ⟨x, y⟩` is a period datum for it, with the
same Gram value `3` at the difference of the edges. -/
example : negOrd₂ (Additive.ofMul two) <
      min (negOrd₂ (Additive.ofMul 1)) (negOrd₂ (Additive.ofMul 1)) ∧
    ((two : ℚˣ) : ℚ) = 1 + 1 ∧ negOrd₂ (negPeriod.Q diff diff) = 3 := by
  refine ⟨?_, by norm_num [two], ?_⟩
  · rw [negOrd₂, AddMonoidHom.neg_apply, ord₂_two, ofMul_one, map_zero]
    norm_num
  · rw [negPeriod.ord_Q, ribbonGram_apply, Fin.sum_univ_two]
    norm_num [diff, twoEdges]

/-- On the two parallel edges, a ribbon-kernel element has opposite values on
the two edges. -/
private theorem ribbonKernel_twoEdges_one (x : ribbonKernel twoEdges) :
    x.1 1 = -x.1 0 := by
  have h := congrFun (mem_ribbonKernel.mp x.2 0) 0
  simp [twoEdges, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at h
  omega

/-- The Gram pairing with the difference of the edges is `3` times the value on
the first edge. -/
private theorem ribbonGram_diff (x : ribbonKernel twoEdges) :
    ribbonGram twoEdges x diff = 3 * x.1 0 := by
  rw [ribbonGram_apply, Fin.sum_univ_two, ribbonKernel_twoEdges_one x]
  norm_num [diff, twoEdges]
  ring

/-- The Gram pairing of the difference of the edges with `y` is `3` times the
value of `y` on the first edge. -/
private theorem ribbonGram_diff_left (y : ribbonKernel twoEdges) :
    ribbonGram twoEdges diff y = 3 * y.1 0 := by
  rw [ribbonGram_apply, Fin.sum_univ_two, ribbonKernel_twoEdges_one y]
  norm_num [diff, twoEdges]
  ring

/-- Base change of units along `ℚ → ℚ` is the identity. -/
private theorem unitsBaseChange_rat (a : Additive ℚˣ) :
    unitsBaseChange ℚ ℚ a = a := by
  obtain ⟨u, rfl⟩ : ∃ u : ℚˣ, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
  simp

/-- The base-changed periods of the two-edge datum. -/
private theorem QL_twoEdges (x y : ribbonKernel twoEdges) :
    twoEdgesPeriod.QL x y = ribbonGram twoEdges x y • Additive.ofMul two := by
  rw [PeriodDatum.QL_apply, unitsBaseChange_rat]
  rfl

/-- The torus point that sends a ribbon-kernel element `y` to `q ^ (y 0)`;
at the difference of the edges it is `q`. -/
private noncomputable def torusAt (q : ℚˣ) : twoEdgesPeriod.TorusPoints :=
  LinearMap.toSpanSingleton ℤ (Additive ℚˣ) (Additive.ofMul q) ∘ₗ
    LinearMap.proj 0 ∘ₗ (ribbonKernel twoEdges).subtype

private theorem torusAt_apply (q : ℚˣ) (y : ribbonKernel twoEdges) :
    torusAt q y = y.1 0 • Additive.ofMul q :=
  rfl

/-- The `3`-adic valuation on the units of `ℚ`. -/
private noncomputable def ord₃ : Additive ℚˣ →+ ℤ :=
  AddMonoidHom.mk' (fun u => padicValRat 3 ((Additive.toMul u : ℚˣ) : ℚ))
    fun u v => by
      simp [padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]

/-- The unit `3` of `ℚ`. -/
private def three : ℚˣ := Units.mk0 3 three_ne_zero

private theorem ord₃_two : ord₃ (Additive.ofMul two) = 0 := by
  show padicValRat 3 ((two : ℚˣ) : ℚ) = 0
  rw [two, Units.val_mk0]
  norm_num [padicValRat]

private theorem ord₃_three : ord₃ (Additive.ofMul three) = 1 := by
  show padicValRat 3 ((three : ℚˣ) : ℚ) = 1
  rw [three, Units.val_mk0]
  exact_mod_cast padicValRat.self (p := 3) (by norm_num)

/-- A torus point in the period lattice takes a value of `2`-adic valuation
divisible by `3` at the difference of the edges: the periods there are the
powers of `8`. -/
private theorem ord₂_of_mem_periodLattice {t : twoEdgesPeriod.TorusPoints}
    (ht : t ∈ twoEdgesPeriod.periodLattice) : (3 : ℤ) ∣ ord₂ (t diff) := by
  obtain ⟨x, rfl⟩ := ht
  rw [QL_twoEdges, map_zsmul, ord₂_two, ribbonGram_diff]
  exact ⟨x.1 0, by ring⟩

/-- A torus point in the period lattice takes a value of `3`-adic valuation `0`
at the difference of the edges. -/
private theorem ord₃_of_mem_periodLattice {t : twoEdgesPeriod.TorusPoints}
    (ht : t ∈ twoEdgesPeriod.periodLattice) : ord₃ (t diff) = 0 := by
  obtain ⟨x, rfl⟩ := ht
  rw [QL_twoEdges, map_zsmul, ord₃_two, smul_zero]

/-- `torusAt 2` is not a period: its value `2` at the difference of the edges
is not a power of `8`. -/
private theorem torusAt_two_not_mem :
    torusAt two ∉ twoEdgesPeriod.periodLattice := fun h => by
  have h3 := ord₂_of_mem_periodLattice h
  rw [torusAt_apply, map_zsmul, ord₂_two] at h3
  norm_num [diff] at h3

/-- `3 • torusAt 2` is the period of the difference of the edges. -/
private theorem three_smul_torusAt_two :
    (3 : ℤ) • torusAt two = twoEdgesPeriod.QL diff := by
  ext y
  rw [LinearMap.smul_apply, torusAt_apply, QL_twoEdges, ribbonGram_diff_left,
    smul_smul]

/-- A nonzero torsion class. The class of `torusAt 2` in `JacPoints` has order
`3`: `torusAt 2` lies in `U`, outside the period lattice. -/
example : torusAt two ∈ twoEdgesPeriod.U ∧
    torusAt two ∉ twoEdgesPeriod.periodLattice ∧
    addOrderOf (twoEdgesPeriod.periodLattice.mkQ (torusAt two)) = 3 := by
  have h3 : (3 : ℕ) • twoEdgesPeriod.periodLattice.mkQ (torusAt two) = 0 := by
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← natCast_zsmul, Nat.cast_ofNat, three_smul_torusAt_two]
    exact LinearMap.mem_range_self _ _
  have hne : twoEdgesPeriod.periodLattice.mkQ (torusAt two) ≠ 0 := by
    rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact torusAt_two_not_mem
  refine ⟨?_, torusAt_two_not_mem, addOrderOf_eq_prime h3 hne⟩
  show twoEdgesPeriod.periodLattice.mkQ (torusAt two) ∈
    Submodule.torsion ℤ twoEdgesPeriod.JacPoints
  rw [Submodule.mem_torsion_iff]
  refine ⟨⟨3, mem_nonZeroDivisors_of_ne_zero three_ne_zero⟩, ?_⟩
  rw [Submonoid.mk_smul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, natCast_zsmul]
  exact h3

/-- A nontorsion class. `torusAt 3` lies outside `U`: no nonzero multiple of it
is a period, since its value `3` at the difference of the edges has `3`-adic
valuation `1` and the periods there have valuation `0`. -/
example : torusAt three ∉ twoEdgesPeriod.U := by
  intro h
  change twoEdgesPeriod.periodLattice.mkQ (torusAt three) ∈
    Submodule.torsion ℤ twoEdgesPeriod.JacPoints at h
  rw [Submodule.mem_torsion_iff] at h
  obtain ⟨⟨a, ha⟩, hax⟩ := h
  rw [Submonoid.mk_smul, ← map_zsmul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hax
  have h0 := ord₃_of_mem_periodLattice hax
  rw [LinearMap.smul_apply, torusAt_apply, smul_smul, map_zsmul, ord₃_three]
    at h0
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  norm_num [diff] at h0
  exact ha0 h0

/-- The projection `π` into `JacPoints` makes `JacPoints` capture exactly its
own torsion through `U`. -/
private theorem isTorsionOf_jacPoints {E V : Type} [Fintype E] [DecidableEq V]
    {D : DegeneracyData E V} {K L : Type} [Field K] [Field L] [Algebra K L]
    {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord) :
    P.IsTorsionOf P.JacPoints := by
  refine ⟨P.π.toAddMonoidHom, fun t ht => ?_, fun u => ?_, fun u => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P.periodLattice t
    obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
    refine ⟨⟨x, ?_⟩, rfl⟩
    show P.periodLattice.mkQ x ∈ Submodule.torsion ℤ P.JacPoints
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    rw [Submonoid.mk_smul, natCast_zsmul]
    exact hnx
  · obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff _).mp u.2
    exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr
      ⟨a, nonZeroDivisors.ne_zero ha, hau⟩
  · show P.periodLattice.mkQ u = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- A positive `IsTorsionOf`: `JacPoints` of the two-edge datum. -/
example : twoEdgesPeriod.IsTorsionOf twoEdgesPeriod.JacPoints :=
  isTorsionOf_jacPoints twoEdgesPeriod

/-- The zero target fails for the two-edge datum: `torusAt 2` lies in `U`
outside the period lattice, so no map to a one-point group has the period
lattice as its kernel. -/
example : ¬ twoEdgesPeriod.IsTorsionOf Unit := by
  rintro ⟨e, -, -, he⟩
  have hU : torusAt two ∈ twoEdgesPeriod.U := by
    show twoEdgesPeriod.periodLattice.mkQ (torusAt two) ∈
      Submodule.torsion ℤ twoEdgesPeriod.JacPoints
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨3, mem_nonZeroDivisors_of_ne_zero three_ne_zero⟩, ?_⟩
    rw [Submonoid.mk_smul, ← map_zsmul, three_smul_torusAt_two,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _
  exact torusAt_two_not_mem ((he ⟨_, hU⟩).mp (Subsingleton.elim _ _))

/-- The target need not be a torsion group: adding a free summand `ℤ` to
`JacPoints` keeps `IsTorsionOf`. -/
example {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) : P.IsTorsionOf (P.JacPoints × ℤ) := by
  obtain ⟨e, hrange, htors, hker⟩ := isTorsionOf_jacPoints P
  refine ⟨e.prod 0, fun t ht => ?_, fun u => ?_, fun u => ?_⟩
  · obtain ⟨u, hu⟩ := hrange t.1 ht.fst
    have h2 : t.2 = 0 := by
      obtain ⟨n, hn, hnt⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht.snd
      rw [nsmul_eq_mul] at hnt
      exact (mul_eq_zero.mp hnt).resolve_left (by exact_mod_cast hn.ne')
    exact ⟨u, Prod.ext hu h2.symm⟩
  · exact (htors u).prod_mk IsOfFinAddOrder.zero
  · rw [← hker u, AddMonoidHom.prod_apply, Prod.mk_eq_zero, AddMonoidHom.zero_apply]
    exact and_iff_left rfl

/-- Three parallel edges from `0` to `1`, of width `1`. -/
private def threeEdges : DegeneracyData (Fin 3) (Fin 2) where
  a _ := 0
  b _ := 1
  w _ := 1

/-- The cyclic shift `(x₀, x₁, x₂) ↦ (x₂, x₀, x₁)` of the three edges. -/
private def cycMat : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

private theorem cycMat_mulVec (x : Fin 3 → ℤ) :
    cycMat.mulVec x = ![x 2, x 0, x 1] := by
  ext i
  fin_cases i <;> simp [cycMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Both degeneracy pushforwards of the three edges add up their values. -/
private theorem jointDelta_threeEdges (i : Fin 2) (x : Fin 3 → ℤ) (v : Fin 2) :
    jointDelta threeEdges i x v = if v = i then x 0 + x 1 + x 2 else 0 := by
  fin_cases i <;> fin_cases v <;>
    simp [threeEdges, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

/-- The cyclic shift on edges with the identity on vertices, as Hecke data with
no bad prime. -/
private def cycHecke : HeckeData threeEdges where
  T _ := cycMat
  Tv _ := 1
  comm _ _ := Commute.refl _
  commv _ _ := Commute.refl _
  S := ∅
  good_equivariant _ _ i x := by
    ext v
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.one_mulVec,
      jointDelta_threeEdges, jointDelta_threeEdges, cycMat_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    split_ifs <;> ring
  kernel_stable _ x hx i := by
    ext v
    have h := congrFun (hx i) v
    rw [jointDelta_threeEdges] at h ⊢
    rw [Matrix.mulVecLin_apply, cycMat_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at h ⊢
    split_ifs at h ⊢ <;> linarith

/-- The period datum `Q x y = 2 ^ ⟨x, y⟩` on the three parallel edges, for the
`2`-adic valuation. -/
private noncomputable def threeEdgesPeriod : PeriodDatum threeEdges ℚ ℚ ord₂ where
  Q := (ribbonGram threeEdges).compr₂
    (LinearMap.toSpanSingleton ℤ (Additive ℚˣ) (Additive.ofMul two))
  Q_symm x y := by
    simp only [LinearMap.compr₂_apply, ribbonGram_apply]
    congr 1
    exact Finset.sum_congr rfl fun e _ => by ring
  ord_Q x y := by
    rw [LinearMap.compr₂_apply, LinearMap.toSpanSingleton_apply, map_zsmul,
      ord₂_two, smul_eq_mul, mul_one]

private theorem threeEdgesPeriod_Q (x y : ribbonKernel threeEdges) :
    threeEdgesPeriod.Q x y =
      (x.1 0 * y.1 0 + x.1 1 * y.1 1 + x.1 2 * y.1 2) • Additive.ofMul two := by
  change ribbonGram threeEdges x y • (Additive.ofMul two : Additive ℚˣ) = _
  rw [ribbonGram_apply, Fin.sum_univ_three]
  simp [threeEdges]

private theorem heckeKernelMap_cycHecke (ℓ : Nat.Primes)
    (y : ribbonKernel threeEdges) :
    (heckeKernelMap cycHecke ℓ y).1 = ![y.1 2, y.1 0, y.1 1] :=
  cycMat_mulVec y.1

/-- The prime `2`. -/
private def prime2 : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- `(1, -1, 0)` lies in the ribbon kernel of the three edges. -/
private theorem e01_mem : (![1, -1, 0] : Fin 3 → ℤ) ∈ ribbonKernel threeEdges := by
  rw [mem_ribbonKernel]
  intro i
  ext v
  rw [jointDelta_threeEdges]
  simp

/-- `(0, 1, -1)` lies in the ribbon kernel of the three edges. -/
private theorem e12_mem : (![0, 1, -1] : Fin 3 → ℤ) ∈ ribbonKernel threeEdges := by
  rw [mem_ribbonKernel]
  intro i
  ext v
  rw [jointDelta_threeEdges]
  simp

/-- The witness of Hecke adjointability need not be the Hecke translate. For
the cyclic shift `T` of three parallel edges and `Q x y = 2 ^ ⟨x, y⟩`, the
witness for `y` is the inverse shift of `y` (the shift applied twice), while
`Q y (T z) ≠ Q (T y) z` for `y = (1, -1, 0)` and `z = (0, 1, -1)`. -/
example : threeEdgesPeriod.HeckeAdjointable cycHecke ∧
    threeEdgesPeriod.Q ⟨_, e01_mem⟩ (heckeKernelMap cycHecke prime2 ⟨_, e12_mem⟩) ≠
      threeEdgesPeriod.Q (heckeKernelMap cycHecke prime2 ⟨_, e01_mem⟩)
        ⟨_, e12_mem⟩ := by
  refine ⟨fun ℓ y => ⟨heckeKernelMap cycHecke ℓ (heckeKernelMap cycHecke ℓ y),
    fun z => ?_⟩, fun h => ?_⟩
  · rw [threeEdgesPeriod_Q, threeEdgesPeriod_Q, heckeKernelMap_cycHecke,
      heckeKernelMap_cycHecke, heckeKernelMap_cycHecke]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 1
    ring
  · have h' := congrArg ord₂ h
    rw [threeEdgesPeriod_Q, threeEdgesPeriod_Q, heckeKernelMap_cycHecke,
      heckeKernelMap_cycHecke, map_zsmul, map_zsmul, ord₂_two] at h'
    norm_num at h'

/-- The trivial action of the trivial group on `Fin 3`. -/
local instance : MulAction Unit (Fin 3) where
  smul _ w := w
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance : GraphAction Unit (SimpleGraph.pathGraph 3) :=
  ⟨fun _ _ _ h => h⟩

/-- The dart `0 → 1` of the path `0 - 1 - 2`. -/
private def d₀₁ : (SimpleGraph.pathGraph 3).Dart :=
  ⟨(0, 1), by simp [SimpleGraph.pathGraph_adj]⟩

/-- The dart `1 → 0` of the path `0 - 1 - 2`. -/
private def d₁₀ : (SimpleGraph.pathGraph 3).Dart :=
  ⟨(1, 0), by simp [SimpleGraph.pathGraph_adj]⟩

/-- The dart `1 → 2` of the path `0 - 1 - 2`. -/
private def d₁₂ : (SimpleGraph.pathGraph 3).Dart :=
  ⟨(1, 2), by simp [SimpleGraph.pathGraph_adj]⟩

private theorem eq_of_mk_vert_eq {v w : Fin 3}
    (h : (Quotient.mk'' v : QuotVert Unit (Fin 3)) = Quotient.mk'' w) :
    v = w := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨_, hg⟩ := h
  exact hg.symm

private theorem eq_of_mk_dart_eq {d d' : (SimpleGraph.pathGraph 3).Dart}
    (h : (Quotient.mk'' d : QuotEdge Unit (SimpleGraph.pathGraph 3)) =
      Quotient.mk'' d') :
    d = d' := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨_, hg⟩ := h
  exact hg.symm

/-- `formalU` is not symmetric. Under the trivial action on the path
`0 - 1 - 2`, the dart `0 → 1` continues by `1 → 2`, so the entry at
`(0 → 1, 1 → 2)` is `1`, while `1 → 2` does not continue by `0 → 1`, so the
entry at `(1 → 2, 0 → 1)` is `0`. The entry at `(0 → 1, 1 → 0)` is `0` too,
because `formalU` does not backtrack. -/
example [Fintype (QuotEdge Unit (SimpleGraph.pathGraph 3))]
    [DecidableEq (QuotEdge Unit (SimpleGraph.pathGraph 3))]
    [Fintype (QuotVert Unit (Fin 3))] [DecidableEq (QuotVert Unit (Fin 3))] :
    formalU Unit (SimpleGraph.pathGraph 3) (fun _ => inferInstance)
        (Quotient.mk'' d₀₁) (Quotient.mk'' d₁₂) = 1 ∧
      formalU Unit (SimpleGraph.pathGraph 3) (fun _ => inferInstance)
        (Quotient.mk'' d₁₂) (Quotient.mk'' d₀₁) = 0 ∧
      formalU Unit (SimpleGraph.pathGraph 3) (fun _ => inferInstance)
        (Quotient.mk'' d₀₁) (Quotient.mk'' d₁₀) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [formalU_apply, ite_eq_left]
    refine ⟨rfl, fun h => ?_⟩
    have h20 : (2 : Fin 3) = 0 :=
      congrArg (fun d : (SimpleGraph.pathGraph 3).Dart => d.fst)
        (eq_of_mk_dart_eq h)
    exact absurd h20 (by decide)
  · rw [formalU_apply, ite_eq_right]
    rintro ⟨h, -⟩
    exact absurd (eq_of_mk_vert_eq (v := 2) (w := 0) h) (by decide)
  · rw [formalU_apply, ite_eq_right]
    rintro ⟨-, h⟩
    exact h rfl

/-- `U` is the preimage of the torsion of `JacPoints`, so it contains the
period lattice. -/
example {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) : P.periodLattice ≤ P.U := by
  intro x hx
  show P.periodLattice.mkQ x ∈ Submodule.torsion ℤ P.JacPoints
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx]
  exact zero_mem _

/-- Base change of units is the identity on `ℚ`. -/
example (u : ℚˣ) :
    unitsBaseChange ℚ ℚ (Additive.ofMul u) = Additive.ofMul u := by
  simp

end MumfordPeriodTest
