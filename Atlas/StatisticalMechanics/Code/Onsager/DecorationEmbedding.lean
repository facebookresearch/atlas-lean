/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationEdgeComponent










namespace StatMech.Onsager


def ons_decEmbedOffset (mu : Fin 4) : ℕ × ℕ :=
  match mu with
  | 0 => (6, 4)
  | 1 => (4, 6)
  | 2 => (2, 4)
  | 3 => (4, 2)


def ons_decEmbedVertex (L : ℕ) (d : ons_Dart L) :
    ZMod (8 * L) × ZMod (8 * L) :=
  ((8 * d.1.1.val + (ons_decEmbedOffset d.2).1 : ℕ),
    (8 * d.1.2.val + (ons_decEmbedOffset d.2).2 : ℕ))

@[simp] theorem ons_decEmbedOffset_fst_le (mu : Fin 4) :
    (ons_decEmbedOffset mu).1 ≤ 6 := by
  fin_cases mu <;> decide

@[simp] theorem ons_decEmbedOffset_snd_le (mu : Fin 4) :
    (ons_decEmbedOffset mu).2 ≤ 6 := by
  fin_cases mu <;> decide

theorem ons_decEmbedCoord_lt (L : ℕ) [Fact (2 < L)]
    (z : ZMod L) (c : ℕ) (hc : c ≤ 6) :
    8 * z.val + c < 8 * L := by
  have hz := z.val_lt
  omega

@[simp] theorem ons_decEmbedVertex_fst_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    (ons_decEmbedVertex L d).1.val =
      8 * d.1.1.val + (ons_decEmbedOffset d.2).1 := by
  unfold ons_decEmbedVertex
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt
    (ons_decEmbedCoord_lt L d.1.1 _ (ons_decEmbedOffset_fst_le d.2))

@[simp] theorem ons_decEmbedVertex_snd_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    (ons_decEmbedVertex L d).2.val =
      8 * d.1.2.val + (ons_decEmbedOffset d.2).2 := by
  unfold ons_decEmbedVertex
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt
    (ons_decEmbedCoord_lt L d.1.2 _ (ons_decEmbedOffset_snd_le d.2))


theorem ons_decEmbedVertex_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (ons_decEmbedVertex L) := by
  rintro ⟨⟨x, y⟩, mu⟩ ⟨⟨x', y'⟩, nu⟩ h
  have hx := congrArg (fun p => p.1.val) h
  have hy := congrArg (fun p => p.2.val) h
  simp only [ons_decEmbedVertex_fst_val, ons_decEmbedVertex_snd_val] at hx hy
  fin_cases mu <;> fin_cases nu <;>
    simp only [ons_decEmbedOffset] at hx hy ⊢
  all_goals
    have hxeq : x = x' := by
      apply ZMod.val_injective
      omega
    have hyeq : y = y' := by
      apply ZMod.val_injective
      omega
    simp [hxeq, hyeq] <;> omega


def ons_decEdgeRouteDirs (L : ℕ) (d e : ons_Dart L) : Fin 4 → Fin 4 :=
  if e = ons_dartRev L d then fun _ => d.2
  else
    match d.2, e.2 with
    | 0, 1 => ![1, 1, 2, 2]
    | 1, 0 => ![0, 0, 3, 3]
    | 1, 2 => ![2, 2, 3, 3]
    | 2, 1 => ![1, 1, 0, 0]
    | 2, 3 => ![3, 3, 0, 0]
    | 3, 2 => ![2, 2, 1, 1]
    | _, _ => ![0, 0, 0, 0]


def ons_fourDirSteps (N : ℕ) (r : Fin 4 → Fin 4)
    (p : ZMod N × ZMod N) : ZMod N × ZMod N :=
  ons_dirStep N (r 3)
    (ons_dirStep N (r 2)
      (ons_dirStep N (r 1) (ons_dirStep N (r 0) p)))

theorem ons_eight_zmodCast_add_one
    (L : ℕ) [Fact (2 < L)] (z : ZMod L) :
    (8 : ZMod (8 * L)) * ZMod.cast z + 8 =
      8 * ZMod.cast (z + 1) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  by_cases hz : z = -1
  · rw [hz, neg_add_cancel, ZMod.cast_zero, mul_zero]
    rw [ZMod.cast_eq_val, ons_zmod_val_neg_one]
    push_cast
    rw [Nat.cast_sub hL]
    have hmod : (8 : ZMod (8 * L)) * (L : ZMod (8 * L)) = 0 := by
      calc
        (8 : ZMod (8 * L)) * (L : ZMod (8 * L)) =
            ((8 : ℕ) : ZMod (8 * L)) * (L : ZMod (8 * L)) := by norm_num
        _ = ((8 * L : ℕ) : ZMod (8 * L)) := (Nat.cast_mul 8 L).symm
        _ = 0 := ZMod.natCast_self _
    linear_combination hmod
  · have hv : z.val + 1 < L := by
      have hne : z.val ≠ L - 1 := by
        intro h
        apply hz
        apply ZMod.val_injective
        rw [h, ons_zmod_val_neg_one]
      have hzlt := z.val_lt
      omega
    have hval : (z + 1).val = z.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, hval]
    push_cast
    ring

theorem ons_eight_zmodCast_sub_one
    (L : ℕ) [Fact (2 < L)] (z : ZMod L) :
    (8 : ZMod (8 * L)) * ZMod.cast z - 8 =
      8 * ZMod.cast (z - 1) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  by_cases hz : z = 0
  · rw [hz, zero_sub, ZMod.cast_zero, mul_zero, zero_sub]
    rw [ZMod.cast_eq_val, ons_zmod_val_neg_one]
    push_cast
    rw [Nat.cast_sub hL]
    have hmod : (8 : ZMod (8 * L)) * (L : ZMod (8 * L)) = 0 := by
      calc
        (8 : ZMod (8 * L)) * (L : ZMod (8 * L)) =
            ((8 : ℕ) : ZMod (8 * L)) * (L : ZMod (8 * L)) := by norm_num
        _ = ((8 * L : ℕ) : ZMod (8 * L)) := (Nat.cast_mul 8 L).symm
        _ = 0 := ZMod.natCast_self _
    linear_combination -hmod
  · have hzval : 1 ≤ z.val := by
      have : z.val ≠ 0 := by
        intro h
        exact hz ((ZMod.val_eq_zero z).mp h)
      omega
    have hval : (z - 1).val = z.val - 1 := by
      have hone : (1 : ZMod L).val ≤ z.val := by
        rw [ZMod.val_one]
        exact hzval
      rw [ZMod.val_sub hone, ZMod.val_one]
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, hval]
    push_cast
    rw [Nat.cast_sub hzval]
    ring



theorem ons_decEdgeRoute_endpoint
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    ons_fourDirSteps (8 * L) (ons_decEdgeRouteDirs L d e)
        (ons_decEmbedVertex L d) =
      ons_decEmbedVertex L e := by
  change ons_decAdj L d e at hde
  rcases hde with hrev | hint
  · subst e
    rcases d with ⟨⟨x, y⟩, mu⟩
    fin_cases mu <;>
      simp [ons_decEdgeRouteDirs, ons_fourDirSteps, ons_decEmbedVertex,
        ons_decEmbedOffset, ons_dartRev, ons_dirStep] <;>
      first
      | linear_combination ons_eight_zmodCast_add_one L x
      | linear_combination ons_eight_zmodCast_add_one L y
      | linear_combination ons_eight_zmodCast_sub_one L x
      | linear_combination ons_eight_zmodCast_sub_one L y
  · rcases d with ⟨p, mu⟩
    rcases e with ⟨q, nu⟩
    have hpq : p = q := hint.1
    subst q
    fin_cases mu <;> fin_cases nu <;>
      simp [ons_decInternalAdj, ons_decEdgeRouteDirs, ons_fourDirSteps,
        ons_decEmbedVertex, ons_decEmbedOffset, ons_dartRev, ons_dirStep] at hint ⊢ <;>
      ring_nf <;> simp


theorem ons_torusAdj_dirStep (N : ℕ) [Fact (2 < N)]
    (p : ZMod N × ZMod N) (mu : Fin 4) :
    (onsTorusGraph N).Adj p (ons_dirStep N mu p) := by
  rcases p with ⟨x, y⟩
  fin_cases mu <;> simp [onsTorusGraph, onsTorusAdj, ons_dirStep] <;> ring


def ons_fourDirStepWalk (N : ℕ) [Fact (2 < N)]
    (r : Fin 4 → Fin 4) (p : ZMod N × ZMod N) :
    (onsTorusGraph N).Walk p (ons_fourDirSteps N r p) :=
  .cons (ons_torusAdj_dirStep N p (r 0))
    (.cons (ons_torusAdj_dirStep N (ons_dirStep N (r 0) p) (r 1))
      (.cons (ons_torusAdj_dirStep N
          (ons_dirStep N (r 1) (ons_dirStep N (r 0) p)) (r 2))
        (.cons (ons_torusAdj_dirStep N
            (ons_dirStep N (r 2)
              (ons_dirStep N (r 1) (ons_dirStep N (r 0) p))) (r 3))
          .nil)))


def ons_decEmbedGraph (L : ℕ) [Fact (2 < L)] :
    SimpleGraph (ZMod (8 * L) × ZMod (8 * L)) := by
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  exact onsTorusGraph (8 * L)

instance (L : ℕ) [Fact (2 < L)] : DecidableRel (ons_decEmbedGraph L).Adj := by
  unfold ons_decEmbedGraph
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  infer_instance


def ons_decEdgeRoute (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEmbedGraph L).Walk
      (ons_decEmbedVertex L d) (ons_decEmbedVertex L e) := by
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  let w : (ons_decEmbedGraph L).Walk (ons_decEmbedVertex L d)
      (ons_fourDirSteps (8 * L) (ons_decEdgeRouteDirs L d e)
        (ons_decEmbedVertex L d)) := by
    simpa [ons_decEmbedGraph] using
      ons_fourDirStepWalk (8 * L) (ons_decEdgeRouteDirs L d e)
        (ons_decEmbedVertex L d)
  exact w.copy rfl (ons_decEdgeRoute_endpoint L d e hde)

@[simp] theorem ons_fourDirStepWalk_length
    (N : ℕ) [Fact (2 < N)] (r : Fin 4 → Fin 4)
    (p : ZMod N × ZMod N) :
    (ons_fourDirStepWalk N r p).length = 4 := by
  rfl

@[simp] theorem ons_decEdgeRoute_length
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).length = 4 := by
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  simp only [ons_decEdgeRoute, SimpleGraph.Walk.length_copy]
  exact ons_fourDirStepWalk_length (8 * L)
    (ons_decEdgeRouteDirs L d e) (ons_decEmbedVertex L d)


def ons_decEdgeRouteVertices
    (L : ℕ) (d e : ons_Dart L) : List (ZMod (8 * L) × ZMod (8 * L)) :=
  let r := ons_decEdgeRouteDirs L d e
  let p₀ := ons_decEmbedVertex L d
  let p₁ := ons_dirStep (8 * L) (r 0) p₀
  let p₂ := ons_dirStep (8 * L) (r 1) p₁
  let p₃ := ons_dirStep (8 * L) (r 2) p₂
  let p₄ := ons_dirStep (8 * L) (r 3) p₃
  [p₀, p₁, p₂, p₃, p₄]

@[simp] theorem ons_decEdgeRoute_support
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).support =
      ons_decEdgeRouteVertices L d e := by
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  simp [ons_decEdgeRoute, ons_fourDirStepWalk,
    ons_decEdgeRouteVertices, ons_fourDirSteps, SimpleGraph.Walk.support]

@[simp] theorem ons_decEdgeRouteVertices_length
    (L : ℕ) (d e : ons_Dart L) :
    (ons_decEdgeRouteVertices L d e).length = 5 := by
  simp [ons_decEdgeRouteVertices]

theorem ons_decEmbed_smallIntCast_eq_iff
    (L : ℕ) [Fact (2 < L)] {a b : ℤ}
    (ha₀ : -4 ≤ a) (ha₁ : a ≤ 12) (hb₀ : -4 ≤ b) (hb₁ : b ≤ 12) :
    (a : ZMod (8 * L)) = (b : ZMod (8 * L)) ↔ a = b := by
  constructor
  · intro hab
    have hz : ((a - b : ℤ) : ZMod (8 * L)) = 0 := by
      push_cast
      linear_combination hab
    rw [CharP.intCast_eq_zero_iff (ZMod (8 * L)) (8 * L)] at hz
    have hL : 24 ≤ (8 * L : ℕ) := by
      have := (Fact.out : 2 < L)
      omega
    have hLz : (24 : ℤ) ≤ (8 * L : ℕ) := by exact_mod_cast hL
    have habs : |a - b| < (8 * L : ℕ) := by
      rw [abs_lt]
      constructor <;> omega
    have hz' : a - b = 0 := Int.eq_zero_of_abs_lt_dvd hz habs
    omega
  · exact congrArg (· : ℤ → ZMod (8 * L))


theorem ons_decEdgeRoute_isPath
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).IsPath := by
  have hne (a b : ℤ) (ha₀ : -4 ≤ a) (ha₁ : a ≤ 12)
      (hb₀ : -4 ≤ b) (hb₁ : b ≤ 12) (hab : a ≠ b) :
      (a : ZMod (8 * L)) ≠ (b : ZMod (8 * L)) := by
    intro h
    exact hab ((ons_decEmbed_smallIntCast_eq_iff L ha₀ ha₁ hb₀ hb₁).mp h)
  have h10 : (1 : ZMod (8 * L)) ≠ 0 := by
    simpa only [Int.cast_one, Int.cast_zero] using
      (hne 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h20 : (2 : ZMod (8 * L)) ≠ 0 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero] using
      (hne 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h68 : (6 : ZMod (8 * L)) ≠ 8 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h69 : (6 : ZMod (8 * L)) ≠ 9 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h610 : (6 : ZMod (8 * L)) ≠ 10 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h21 : (2 : ZMod (8 * L)) ≠ 1 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat, Int.cast_one] using
      (hne 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h2m1 : (2 : ZMod (8 * L)) ≠ -1 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat, Int.cast_neg, Int.cast_one] using
      (hne 2 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h2m2 : (2 : ZMod (8 * L)) ≠ -2 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat, Int.cast_neg] using
      (hne 2 (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h46 : (4 : ZMod (8 * L)) ≠ 6 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h65 : (6 : ZMod (8 * L)) ≠ 5 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h64 : (6 : ZMod (8 * L)) ≠ 4 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h43 : (4 : ZMod (8 * L)) ≠ 3 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h42 : (4 : ZMod (8 * L)) ≠ 2 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h24 : (2 : ZMod (8 * L)) ≠ 4 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  rw [SimpleGraph.Walk.isPath_def, ons_decEdgeRoute_support]
  change ons_decAdj L d e at hde
  rcases hde with hrev | hint
  · subst e
    rcases d with ⟨⟨x, y⟩, mu⟩
    fin_cases mu <;>
      simp [ons_decEdgeRouteVertices, ons_decEdgeRouteDirs,
        ons_decEmbedVertex, ons_decEmbedOffset, ons_dartRev, ons_dirStep] <;>
      ring_nf <;>
      simp [h10, h20, h68, h69, h610, h21, h2m1, h2m2]
  · rcases d with ⟨p, mu⟩
    rcases e with ⟨q, nu⟩
    have hpq : p = q := hint.1
    subst q
    fin_cases mu <;> fin_cases nu <;>
      simp [ons_decInternalAdj, ons_decEdgeRouteVertices,
        ons_decEdgeRouteDirs, ons_decEmbedVertex, ons_decEmbedOffset,
        ons_dartRev, ons_dirStep] at hint ⊢ <;>
      ring_nf <;>
      simp [h10, h46, h65, h64, h43, h42, h24]


structure ons_DecMicroPoint (L : ℕ) where
  cell : ZMod L × ZMod L
  offsetX : Fin 8
  offsetY : Fin 8
deriving DecidableEq

def ons_decMicroVertex (L : ℕ) (z : ons_DecMicroPoint L) :
    ZMod (8 * L) × ZMod (8 * L) :=
  ((8 * z.cell.1.val + z.offsetX.val : ℕ),
    (8 * z.cell.2.val + z.offsetY.val : ℕ))

@[simp] theorem ons_decMicroVertex_fst_val
    (L : ℕ) [Fact (2 < L)] (z : ons_DecMicroPoint L) :
    (ons_decMicroVertex L z).1.val = 8 * z.cell.1.val + z.offsetX.val := by
  unfold ons_decMicroVertex
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hz := z.cell.1.val_lt
  have ho := z.offsetX.isLt
  omega

@[simp] theorem ons_decMicroVertex_snd_val
    (L : ℕ) [Fact (2 < L)] (z : ons_DecMicroPoint L) :
    (ons_decMicroVertex L z).2.val = 8 * z.cell.2.val + z.offsetY.val := by
  unfold ons_decMicroVertex
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hz := z.cell.2.val_lt
  have ho := z.offsetY.isLt
  omega

theorem ons_decMicroVertex_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (ons_decMicroVertex L) := by
  intro z w h
  have hx := congrArg (fun p => p.1.val) h
  have hy := congrArg (fun p => p.2.val) h
  simp only [ons_decMicroVertex_fst_val] at hx
  simp only [ons_decMicroVertex_snd_val] at hy
  have hcx : z.cell.1 = w.cell.1 := by
    apply ZMod.val_injective
    omega
  have hcy : z.cell.2 = w.cell.2 := by
    apply ZMod.val_injective
    omega
  have hox : z.offsetX = w.offsetX := by
    apply Fin.ext
    omega
  have hoy : z.offsetY = w.offsetY := by
    apply Fin.ext
    omega
  have hc : z.cell = w.cell := Prod.ext hcx hcy
  cases z
  cases w
  simp_all



def ons_decEdgeInteriorData (L : ℕ) (d e : ons_Dart L) :
    List (ons_DecMicroPoint L) :=
  if e = ons_dartRev L d then
    match d.2 with
    | 0 => [⟨d.1, 7, 4⟩, ⟨ons_dirStep L 0 d.1, 0, 4⟩,
      ⟨ons_dirStep L 0 d.1, 1, 4⟩]
    | 1 => [⟨d.1, 4, 7⟩, ⟨ons_dirStep L 1 d.1, 4, 0⟩,
      ⟨ons_dirStep L 1 d.1, 4, 1⟩]
    | 2 => [⟨d.1, 1, 4⟩, ⟨d.1, 0, 4⟩,
      ⟨ons_dirStep L 2 d.1, 7, 4⟩]
    | 3 => [⟨d.1, 4, 1⟩, ⟨d.1, 4, 0⟩,
      ⟨ons_dirStep L 3 d.1, 4, 7⟩]
  else
    match d.2, e.2 with
    | 0, 1 => [⟨d.1, 6, 5⟩, ⟨d.1, 6, 6⟩, ⟨d.1, 5, 6⟩]
    | 1, 0 => [⟨d.1, 5, 6⟩, ⟨d.1, 6, 6⟩, ⟨d.1, 6, 5⟩]
    | 1, 2 => [⟨d.1, 3, 6⟩, ⟨d.1, 2, 6⟩, ⟨d.1, 2, 5⟩]
    | 2, 1 => [⟨d.1, 2, 5⟩, ⟨d.1, 2, 6⟩, ⟨d.1, 3, 6⟩]
    | 2, 3 => [⟨d.1, 2, 3⟩, ⟨d.1, 2, 2⟩, ⟨d.1, 3, 2⟩]
    | 3, 2 => [⟨d.1, 3, 2⟩, ⟨d.1, 2, 2⟩, ⟨d.1, 2, 3⟩]
    | _, _ => []

theorem ons_decInternalRoute_interior_support
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hint : ons_decInternalAdj d e) :
    (ons_decEdgeRouteVertices L d e).tail.dropLast =
      (ons_decEdgeInteriorData L d e).map (ons_decMicroVertex L) := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  have hpq : p = q := hint.1
  subst q
  have hnotrev : (p, nu) ≠ ons_dartRev L (p, mu) := by
    intro h
    have hs := congrArg (fun d : ons_Dart L => d.1) h
    exact ons_dirStep_ne_self L mu p hs.symm
  fin_cases mu <;> fin_cases nu
  all_goals simp [ons_decInternalAdj] at hint
  all_goals
    simp [ons_decEdgeRouteVertices, ons_decEdgeRouteDirs,
      ons_decEdgeInteriorData, ons_decMicroVertex, ons_decEmbedVertex,
      ons_decEmbedOffset, ons_dartRev, ons_dirStep, hnotrev] <;>
    ring_nf <;> simp



def ons_decMicroCorridorEdge (L : ℕ) (z : ons_DecMicroPoint L) :
    Sym2 (ons_Dart L) :=
  match z.offsetX.val, z.offsetY.val with
  | 7, 4 => s((z.cell, 0), (ons_dirStep L 0 z.cell, 2))
  | 0, 4 => s((ons_dirStep L 2 z.cell, 0), (z.cell, 2))
  | 1, 4 => s((ons_dirStep L 2 z.cell, 0), (z.cell, 2))
  | 4, 7 => s((z.cell, 1), (ons_dirStep L 1 z.cell, 3))
  | 4, 0 => s((ons_dirStep L 3 z.cell, 1), (z.cell, 3))
  | 4, 1 => s((ons_dirStep L 3 z.cell, 1), (z.cell, 3))
  | 6, 5 => s((z.cell, 0), (z.cell, 1))
  | 6, 6 => s((z.cell, 0), (z.cell, 1))
  | 5, 6 => s((z.cell, 0), (z.cell, 1))
  | 3, 6 => s((z.cell, 1), (z.cell, 2))
  | 2, 6 => s((z.cell, 1), (z.cell, 2))
  | 2, 5 => s((z.cell, 1), (z.cell, 2))
  | 2, 3 => s((z.cell, 2), (z.cell, 3))
  | 2, 2 => s((z.cell, 2), (z.cell, 3))
  | 3, 2 => s((z.cell, 2), (z.cell, 3))
  | _, _ => s((z.cell, 0), (z.cell, 1))

theorem ons_decMicroCorridorEdge_of_mem
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) {z : ons_DecMicroPoint L}
    (hz : z ∈ ons_decEdgeInteriorData L d e) :
    ons_decMicroCorridorEdge L z = s(d, e) := by
  change ons_decAdj L d e at hde
  rcases hde with hrev | hint
  · subst e
    rcases d with ⟨p, mu⟩
    fin_cases mu <;>
      simp [ons_decEdgeInteriorData] at hz <;>
      rcases hz with rfl | rfl | rfl <;>
      simp [ons_decMicroCorridorEdge, ons_dartRev, ons_dirStep,
        Sym2.eq_iff] <;> ring
  · rcases d with ⟨p, mu⟩
    rcases e with ⟨q, nu⟩
    have hpq : p = q := hint.1
    subst q
    have hnotrev : (p, nu) ≠ ons_dartRev L (p, mu) := by
      intro h
      have hs := congrArg (fun d : ons_Dart L => d.1) h
      exact ons_dirStep_ne_self L mu p hs.symm
    unfold ons_decEdgeInteriorData at hz
    rw [if_neg hnotrev] at hz
    fin_cases mu <;> fin_cases nu
    all_goals simp [ons_decInternalAdj] at hint
    all_goals simp at hz
    all_goals
      rcases hz with rfl | rfl | rfl <;>
      simp [ons_decMicroCorridorEdge, Sym2.eq_iff]

@[simp] theorem ons_decEdgeRoute_interior_support
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).support.tail.dropLast =
      (ons_decEdgeInteriorData L d e).map (ons_decMicroVertex L) := by
  rw [ons_decEdgeRoute_support]
  change ons_decAdj L d e at hde
  rcases hde with hrev | hint
  · subst e
    rcases d with ⟨⟨x, y⟩, mu⟩
    fin_cases mu <;>
      simp [ons_decEdgeRouteVertices, ons_decEdgeRouteDirs,
        ons_decEdgeInteriorData, ons_decMicroVertex, ons_decEmbedVertex,
        ons_decEmbedOffset, ons_dartRev, ons_dirStep]
    all_goals
      repeat' apply And.intro
      all_goals first
      | simpa [add_comm, mul_comm] using ons_eight_zmodCast_add_one L x
      | simpa [add_comm, mul_comm] using ons_eight_zmodCast_add_one L y
      | have hs := ons_eight_zmodCast_sub_one L x
        simp [sub_eq_add_neg, add_comm, mul_comm] at hs ⊢
        linear_combination hs
      | have hs := ons_eight_zmodCast_sub_one L y
        simp [sub_eq_add_neg, add_comm, mul_comm] at hs ⊢
        linear_combination hs
      | linear_combination ons_eight_zmodCast_add_one L x
      | linear_combination ons_eight_zmodCast_add_one L y
      | linear_combination ons_eight_zmodCast_sub_one L x
      | linear_combination ons_eight_zmodCast_sub_one L y
      | ring
  · exact ons_decInternalRoute_interior_support L d e hint



theorem ons_decEdgeRoute_edge_eq_of_interior_mem
    (L : ℕ) [Fact (2 < L)]
    (d e f g : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e)
    (hfg : (ons_decGraph L).Adj f g)
    {x : ZMod (8 * L) × ZMod (8 * L)}
    (hx : x ∈ (ons_decEdgeRoute L d e hde).support.tail.dropLast)
    (hy : x ∈ (ons_decEdgeRoute L f g hfg).support.tail.dropLast) :
    s(d, e) = s(f, g) := by
  rw [ons_decEdgeRoute_interior_support] at hx hy
  rcases List.mem_map.mp hx with ⟨z, hz, hzx⟩
  rcases List.mem_map.mp hy with ⟨w, hw, hwx⟩
  have hzw : z = w := ons_decMicroVertex_injective L (hzx.trans hwx.symm)
  calc
    s(d, e) = ons_decMicroCorridorEdge L z :=
      (ons_decMicroCorridorEdge_of_mem L d e hde hz).symm
    _ = ons_decMicroCorridorEdge L w := by rw [hzw]
    _ = s(f, g) := ons_decMicroCorridorEdge_of_mem L f g hfg hw

def ons_decInteriorOffsets : Finset (Fin 8 × Fin 8) :=
  {(7, 4), (0, 4), (1, 4), (4, 7), (4, 0), (4, 1),
    (6, 5), (6, 6), (5, 6), (3, 6), (2, 6), (2, 5),
    (2, 3), (2, 2), (3, 2)}

theorem ons_decEdgeInteriorData_offset_mem
    (L : ℕ) (d e : ons_Dart L) {z : ons_DecMicroPoint L}
    (hz : z ∈ ons_decEdgeInteriorData L d e) :
    (z.offsetX, z.offsetY) ∈ ons_decInteriorOffsets := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  unfold ons_decEdgeInteriorData at hz
  split at hz
  · fin_cases mu <;> simp at hz
    all_goals
      rcases hz with rfl | rfl | rfl <;>
      simp [ons_decInteriorOffsets]
  · fin_cases mu <;> fin_cases nu <;> simp at hz
    all_goals
      rcases hz with rfl | rfl | rfl <;>
      simp [ons_decInteriorOffsets]

def ons_decPortMicroPoint (L : ℕ) (d : ons_Dart L) :
    ons_DecMicroPoint L :=
  match d.2 with
  | 0 => ⟨d.1, 6, 4⟩
  | 1 => ⟨d.1, 4, 6⟩
  | 2 => ⟨d.1, 2, 4⟩
  | 3 => ⟨d.1, 4, 2⟩

@[simp] theorem ons_decMicroVertex_port
    (L : ℕ) (d : ons_Dart L) :
    ons_decMicroVertex L (ons_decPortMicroPoint L d) =
      ons_decEmbedVertex L d := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decPortMicroPoint, ons_decMicroVertex,
      ons_decEmbedVertex, ons_decEmbedOffset]

theorem ons_decPort_offset_not_mem
    (L : ℕ) (d : ons_Dart L) :
    ((ons_decPortMicroPoint L d).offsetX,
      (ons_decPortMicroPoint L d).offsetY) ∉ ons_decInteriorOffsets := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decPortMicroPoint, ons_decInteriorOffsets]


theorem ons_decEmbedVertex_not_mem_route_interior
    (L : ℕ) [Fact (2 < L)] (d f g : ons_Dart L)
    (hfg : (ons_decGraph L).Adj f g) :
    ons_decEmbedVertex L d ∉
      (ons_decEdgeRoute L f g hfg).support.tail.dropLast := by
  intro hd
  rw [ons_decEdgeRoute_interior_support] at hd
  rcases List.mem_map.mp hd with ⟨z, hz, hzeq⟩
  have hpz : ons_decPortMicroPoint L d = z :=
    ons_decMicroVertex_injective L
      ((ons_decMicroVertex_port L d).trans hzeq.symm)
  apply ons_decPort_offset_not_mem L d
  rw [hpz]
  exact ons_decEdgeInteriorData_offset_mem L f g hz

theorem ons_decEdgeRoute_tail_support
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).support.tail =
      (ons_decEdgeRoute L d e hde).support.tail.dropLast ++
        [ons_decEmbedVertex L e] := by
  rw [ons_decEdgeRoute_support]
  simp [ons_decEdgeRouteVertices]
  exact ons_decEdgeRoute_endpoint L d e hde

def ons_decDartSegment (L : ℕ) [Fact (2 < L)]
    (a : (ons_decGraph L).Dart) :
    List (ZMod (8 * L) × ZMod (8 * L)) :=
  (ons_decEdgeRoute L a.fst a.snd a.adj).support.tail

theorem ons_mem_decDartSegment_iff
    (L : ℕ) [Fact (2 < L)] (a : (ons_decGraph L).Dart)
    (x : ZMod (8 * L) × ZMod (8 * L)) :
    x ∈ ons_decDartSegment L a ↔
      x ∈ (ons_decEdgeRoute L a.fst a.snd a.adj).support.tail.dropLast ∨
        x = ons_decEmbedVertex L a.snd := by
  rw [ons_decDartSegment, ons_decEdgeRoute_tail_support]
  simp

theorem ons_decDartSegment_nodup
    (L : ℕ) [Fact (2 < L)] (a : (ons_decGraph L).Dart) :
    (ons_decDartSegment L a).Nodup := by
  exact (ons_decEdgeRoute_isPath L a.fst a.snd a.adj).support_nodup.tail

theorem ons_decDartSegment_disjoint
    (L : ℕ) [Fact (2 < L)]
    (a b : (ons_decGraph L).Dart)
    (hedge : a.edge ≠ b.edge) (hsnd : a.snd ≠ b.snd) :
    List.Disjoint (ons_decDartSegment L a) (ons_decDartSegment L b) := by
  rw [List.disjoint_left]
  intro x hxa hxb
  rw [ons_mem_decDartSegment_iff] at hxa hxb
  rcases hxa with hxa | hxa <;> rcases hxb with hxb | hxb
  · apply hedge
    exact ons_decEdgeRoute_edge_eq_of_interior_mem L
      a.fst a.snd b.fst b.snd a.adj b.adj hxa hxb
  · subst x
    exact ons_decEmbedVertex_not_mem_route_interior
      L b.snd a.fst a.snd a.adj hxa
  · subst x
    exact ons_decEmbedVertex_not_mem_route_interior
      L a.snd b.fst b.snd b.adj hxb
  · apply hsnd
    exact ons_decEmbedVertex_injective L (hxa.symm.trans hxb)


def ons_decEmbedWalk (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decEmbedGraph L).Walk
      (ons_decEmbedVertex L u) (ons_decEmbedVertex L v) :=
  match p with
  | .nil => .nil
  | .cons huw p =>
      (ons_decEdgeRoute L u _ huw).append (ons_decEmbedWalk L p)

theorem ons_decEmbedWalk_tail_support
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decEmbedWalk L p).support.tail =
      p.darts.flatMap (ons_decDartSegment L) := by
  induction p with
  | nil => simp [ons_decEmbedWalk]
  | @cons u w v huw p ih =>
      simp only [ons_decEmbedWalk, SimpleGraph.Walk.tail_support_append,
        SimpleGraph.Walk.darts_cons, List.flatMap_cons, ih]
      rfl

theorem ons_decEmbedWalk_length_aux
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decEmbedWalk L p).length = 4 * p.length := by
  induction p with
  | nil => simp [ons_decEmbedWalk]
  | @cons u w v huw p ih =>
      simp only [ons_decEmbedWalk, SimpleGraph.Walk.length_append,
        ons_decEdgeRoute_length, ih, SimpleGraph.Walk.length_cons]
      ring

theorem ons_decEmbedWalk_tail_nodup_of_isCycle
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (p : (ons_decGraph L).Walk d d) (hp : p.IsCycle) :
    (ons_decEmbedWalk L p).support.tail.Nodup := by
  rw [ons_decEmbedWalk_tail_support]
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    exact ons_decDartSegment_nodup L a
  · have hedge : p.darts.Pairwise (fun a b => a.edge ≠ b.edge) := by
      have h := hp.edges_nodup
      change (p.darts.map (fun a => a.edge)).Nodup at h
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at h
      exact h
    have hsndMap : (p.darts.map (fun a => a.snd)).Nodup := by
      rw [SimpleGraph.Walk.map_snd_darts]
      exact hp.support_nodup
    have hsnd : p.darts.Pairwise (fun a b => a.snd ≠ b.snd) := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hsndMap
      exact hsndMap
    have hboth : p.darts.Pairwise
        (fun a b => a.edge ≠ b.edge ∧ a.snd ≠ b.snd) :=
      List.pairwise_and_iff.mpr ⟨hedge, hsnd⟩
    exact hboth.imp (fun hab =>
      ons_decDartSegment_disjoint L _ _ hab.1 hab.2)



theorem ons_decEmbedWalk_isCycle
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (p : (ons_decGraph L).Walk d d) (hp : p.IsCycle) :
    (ons_decEmbedWalk L p).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  have hlen : 3 ≤ (ons_decEmbedWalk L p).length := by
    rw [ons_decEmbedWalk_length_aux]
    have := hp.three_le_length
    omega
  refine ⟨?_, hlen⟩
  apply SimpleGraph.Walk.IsPath.mk'
  have hnotnil : ¬(ons_decEmbedWalk L p).Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  rw [(ons_decEmbedWalk L p).support_tail_of_not_nil hnotnil]
  exact ons_decEmbedWalk_tail_nodup_of_isCycle L p hp

@[simp] theorem ons_decEmbedWalk_length
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decEmbedWalk L p).length = 4 * p.length := by
  exact ons_decEmbedWalk_length_aux L p

end StatMech.Onsager
