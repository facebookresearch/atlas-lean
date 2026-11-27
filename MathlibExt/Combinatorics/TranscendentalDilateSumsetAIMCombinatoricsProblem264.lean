/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Algebraic.Defs
import MathlibExt.MeasureTheory.Geometry.BrunnMinkowski
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Sums of a set and a transcendental dilate (AIM additive combinatorics, Problem 4.8)

Problems presented at the AIM workshop on recent trends in additive combinatorics (collected by E.
Croot and V. F. Lev), Problem 4.8 (I. Łaba): suppose that `α` is transcendental and `|A| = n`. What
is the best lower bound for `|A + αA|`? Remarks: Konyagin and Łaba have shown that this cardinality
is `≫ n log n / log log n`; the best example (lowest known cardinality) is `n e^{c √(log n)}`.

This file proves `transcendentalDilateLowerBound_holds`, the theorem of D. Conlon and J. Lim:
`|A + α • A| ≥ e^{c √(log |A|)} |A|` for every finite set `A` of reals and every real `α`
transcendental over `ℚ`, with the constant `c = log 2 / 32`.

Source: Problems presented at the workshop on recent trends in additive combinatorics, collected by
E. Croot and V. F. Lev, AIM workshop problem list, Problem 4.8 (I. Łaba),
https://aimath.org/WWN/additivecomb/additivecomb.pdf. UnsolvedMath record UM-20001139
(`AIM-COMBINATORICS-0264`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is a finite set of reals and `α` a real number transcendental over `ℚ`, the setting of the
Konyagin–Łaba bounds and of the resolving theorem. The statement is the lower bound `|A + αA| ≥ e^{c
√(log |A|)} |A|` with an absolute constant `c > 0`, which matches the Konyagin–Łaba example `n e^{c
√(log n)}` up to the constant; the matching construction and the optimal constant are not stated.

## Proof outline

The proof follows Section 2 of D. Conlon and J. Lim, *Sums of transcendental dilates*,
arXiv:2212.10128 (version 2), except for the bound on the number of coordinates, see below. Write
`Φ` for the shift of coordinate vectors, which is multiplication by `X` on coefficient vectors of
polynomials.

* The Krachun–Petrov reduction. The `ℚ[X]`-module spanned by `A`, with `X` acting as
  multiplication by `α`, is finitely generated and torsion free since `α` is transcendental, hence
  free. Encoding its coordinates in disjoint blocks of powers of `X` and clearing denominators
  gives a set `B` of integer coefficient vectors with `|B| = |A|` and `|B + Φ B| ≤ |A + α • A|`.
* Compressions. Compressing in each coordinate keeps `|B|`, does not increase `|B + Φ B|` (by the
  Cauchy–Davenport inequality on each line) and commutes with the shift; compressing in all the
  coordinates in turn gives a down-set of the nonnegative orthant.
* Plünnecke–Ruzsa. For `S = A + Φ A`, `|S + Φ S| ≤ 81 K^8 |A|`, where `K = |A + Φ A| / |A|`
  (one Ruzsa triangle inequality and one Plünnecke–Ruzsa inequality; the paper has `K^10`).
* Projections. For a down-set `S` and a set `I` of coordinates containing no `L` consecutive
  integers, `|S_I|^L ≤ |S + Φ S|^(L - 1)`, where `S_I` is the part of `S` supported on `I`.
* Discrete Brunn–Minkowski. `|X + Y + {0, 1}^D| ≥ 2^D |X|` when `|X| = |Y|`, from the
  Brunn–Minkowski inequality (`MathlibExt.MeasureTheory.Geometry.BrunnMinkowski`) for the unions
  of unit cubes at `X` and `Y`; for a down-set `S`, `|S + {0, 1}^D|` is at most the sum of `|S_J|`
  over all sets `J` of coordinates, which is the form the paper uses.
* Coordinates. The paper bounds the number `d` of coordinates used by `A` with Ruzsa's estimate
  for sums of sets in several dimensions. Instead, the Plünnecke–Ruzsa inequality applied to the
  `h`-fold sums of the shifted unit vectors gives `d ≤ 4 K h` whenever `|A| ≤ 3^h`, which is
  enough for the counting below.
* Splitting the sets `J` of coordinates according to whether they contain `L ≈ √(log |A|)`
  consecutive coordinates used by `A + Φ A`, and comparing with the Brunn–Minkowski lower bound,
  gives a contradiction when `K < e^{c √(log |A|)}` and `√(log |A|) > 16`; smaller sets follow
  from the Cauchy–Davenport inequality `|A + α • A| ≥ 2 |A| - 1`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.TranscendentalDilateSumsetAIMCombinatoricsProblem264Wanted

open scoped Pointwise

/-- **Lower bound for sums of transcendental dilates.** There is a real constant $c > 0$ such that
for every real number $\alpha$ transcendental over $\mathbb{Q}$ and every finite set $A$ of real
numbers,
$$e^{c\sqrt{\log |A|}}\,|A| \le |A + \alpha \cdot A|,$$
where $A + \alpha \cdot A = \{a + \alpha b : a, b \in A\}$. -/
def transcendentalDilateLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (α : ℝ), Transcendental ℚ α → ∀ A : Finset ℝ,
    Real.exp (c * Real.sqrt (Real.log A.card)) * A.card ≤ ((A + α • A).card : ℝ)

noncomputable section Proof

open Finset _root_.MeasureTheory
open scoped ENNReal

/-- Equality of integer coordinate vectors, decided classically; local to this proof section. -/
private local instance instDecidableEqCoordVec : DecidableEq (ℕ → ℤ) := Classical.decEq _

/-- The coordinate shift `Φ`, with `(Φ x) 0 = 0` and `(Φ x) (i + 1) = x i`: on coefficient
vectors of polynomials it is multiplication by `X`. -/
private def shHom : (ℕ → ℤ) →+ (ℕ → ℤ) where
  toFun x i := if i = 0 then 0 else x (i - 1)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; by_cases hi : i = 0 <;> simp [hi]

private lemma shHom_zero (x : ℕ → ℤ) : shHom x 0 = 0 := by simp [shHom]

private lemma shHom_succ (x : ℕ → ℤ) (i : ℕ) : shHom x (i + 1) = x i := by simp [shHom]

private lemma shHom_injective : Function.Injective shHom := by
  intro x y h
  funext i
  simpa [shHom_succ] using congrFun h (i + 1)

/-- The point `x` with its `k`-th coordinate replaced by `0`: two points lie on a common line in
direction `k` exactly when they have the same key. -/
private def key (k : ℕ) (x : ℕ → ℤ) : ℕ → ℤ := Function.update x k 0

/-- The number of points of `A` on the line in direction `k` through `y`. -/
private def fcard (k : ℕ) (A : Finset (ℕ → ℤ)) (y : ℕ → ℤ) : ℕ :=
  #(A.filter (fun a => key k a = key k y))

/-- The compression of `A` in direction `k`: a line in direction `k` meeting `A` in `m` points is
replaced by its points with `k`-th coordinate `0, 1, …, m - 1`. -/
private def comp (k : ℕ) (A : Finset (ℕ → ℤ)) : Finset (ℕ → ℤ) :=
  (A.image (key k)).biUnion
    (fun y => (range (fcard k A y)).image (fun t : ℕ => Function.update y k (t : ℤ)))

private lemma key_key (k : ℕ) (x : ℕ → ℤ) : key k (key k x) = key k x := by simp [key]

private lemma key_update (k : ℕ) (x : ℕ → ℤ) (t : ℤ) : key k (Function.update x k t) = key k x := by
  simp [key]

private lemma update_key (k : ℕ) (x : ℕ → ℤ) : Function.update (key k x) k (x k) = x := by
  simp [key]

private lemma key_apply_of_ne {k i : ℕ} (h : i ≠ k) (x : ℕ → ℤ) : key k x i = x i := by
  simp [key, h]

private lemma key_add (k : ℕ) (x y : ℕ → ℤ) : key k (x + y) = key k x + key k y := by
  funext i; by_cases hi : i = k <;> simp [key, hi]

private lemma fcard_key (k : ℕ) (A : Finset (ℕ → ℤ)) (z : ℕ → ℤ) :
    fcard k A (key k z) = fcard k A z := by
  simp [fcard, key_key]

private lemma fcard_update (k : ℕ) (A : Finset (ℕ → ℤ)) (z : ℕ → ℤ) (t : ℤ) :
    fcard k A (Function.update z k t) = fcard k A z := by
  simp [fcard, key_update]

/-- Two points with the same key and the same `k`-th coordinate are equal. -/
private lemma eq_of_key_eq {k : ℕ} {x y : ℕ → ℤ} (h : key k x = key k y) (hk : x k = y k) :
    x = y := by
  rw [← update_key k x, ← update_key k y, h, hk]

private lemma mem_comp {k : ℕ} {A : Finset (ℕ → ℤ)} {z : ℕ → ℤ} :
    z ∈ comp k A ↔ 0 ≤ z k ∧ z k < fcard k A z := by
  constructor
  · intro hz
    simp only [comp, mem_biUnion, mem_image, mem_range] at hz
    obtain ⟨y, ⟨a, ha, rfl⟩, t, ht, rfl⟩ := hz
    refine ⟨by simp, ?_⟩
    rw [fcard_update, fcard_key, Function.update_self]
    rw [fcard_key] at ht
    exact_mod_cast ht
  · rintro ⟨h0, hlt⟩
    have hpos : 0 < fcard k A z := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    rw [mem_filter] at ha
    simp only [comp, mem_biUnion, mem_image, mem_range]
    refine ⟨key k z, ⟨a, ha.1, ha.2⟩, (z k).toNat, ?_, ?_⟩
    · rw [fcard_key]; omega
    · rw [Int.toNat_of_nonneg h0]; exact update_key k z

private lemma exists_of_mem_comp {k : ℕ} {A : Finset (ℕ → ℤ)} {z : ℕ → ℤ} (hz : z ∈ comp k A) :
    ∃ a ∈ A, key k a = key k z := by
  obtain ⟨h0, hlt⟩ := mem_comp.mp hz
  have hpos : 0 < fcard k A z := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  rw [mem_filter] at ha
  exact ⟨a, ha.1, ha.2⟩

private lemma card_comp (k : ℕ) (A : Finset (ℕ → ℤ)) : #(comp k A) = #A := by
  rw [comp, card_biUnion]
  · rw [card_eq_sum_card_image (key k) A]
    refine sum_congr rfl fun y hy => ?_
    rw [card_image_of_injective, card_range]
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
      simp [fcard, key_key]
    · intro t t' h
      simpa using congrFun h k
  · intro y hy y' hy' hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro z hz hz'
    obtain ⟨t, -, rfl⟩ := mem_image.mp hz
    obtain ⟨t', -, h⟩ := mem_image.mp hz'
    apply hne
    obtain ⟨a, -, rfl⟩ := mem_image.mp hy
    obtain ⟨a', -, rfl⟩ := mem_image.mp hy'
    have := congrArg (key k) h
    simpa [key_update, key_key] using this.symm

private lemma card_comp_add_comp_le (k : ℕ) (A B : Finset (ℕ → ℤ)) :
    #(comp k A + comp k B) ≤ #(A + B) := by
  set T := (A + B).image (key k) with hT
  have hmaps : Set.MapsTo (key k) ↑(comp k A + comp k B) ↑T := by
    intro z hz
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_add.mp hz
    obtain ⟨a, ha, hka⟩ := exists_of_mem_comp ha'
    obtain ⟨b, hb, hkb⟩ := exists_of_mem_comp hb'
    rw [coe_image]
    refine ⟨a + b, mem_add.mpr ⟨a, ha, b, hb, rfl⟩, ?_⟩
    rw [key_add, key_add, hka, hkb]
  rw [card_eq_sum_card_fiberwise hmaps,
    card_eq_sum_card_fiberwise (f := key k) (t := T) (fun x hx => mem_image_of_mem _ hx)]
  refine sum_le_sum fun y hy => ?_
  set P := (A.image (key k) ×ˢ B.image (key k)).filter (fun p => p.1 + p.2 = y) with hPdef
  have hP : P.Nonempty := by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
    exact ⟨(key k a, key k b), mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_image_of_mem _ ha, mem_image_of_mem _ hb⟩, (key_add k a b).symm⟩⟩
  obtain ⟨p, hp, hmax⟩ := P.exists_max_image (fun p => fcard k A p.1 + fcard k B p.2) hP
  obtain ⟨hp1, hp2⟩ := mem_product.mp (mem_filter.mp hp).1
  have hpy : p.1 + p.2 = y := (mem_filter.mp hp).2
  obtain ⟨a0, ha0, hpa⟩ := mem_image.mp hp1
  obtain ⟨b0, hb0, hpb⟩ := mem_image.mp hp2
  -- Claim 1: the compressed fiber is an initial segment of bounded length
  have h1 : #((comp k A + comp k B).filter (fun z => key k z = y)) ≤
      fcard k A p.1 + fcard k B p.2 - 1 := by
    have hsub : (comp k A + comp k B).filter (fun z => key k z = y) ⊆
        (range (fcard k A p.1 + fcard k B p.2 - 1)).image
          (fun t : ℕ => Function.update y k (t : ℤ)) := by
      intro z hz
      rw [mem_filter] at hz
      obtain ⟨hz, hzy⟩ := hz
      obtain ⟨a', ha', b', hb', rfl⟩ := mem_add.mp hz
      obtain ⟨ha0', haf⟩ := mem_comp.mp ha'
      obtain ⟨hb0', hbf⟩ := mem_comp.mp hb'
      obtain ⟨a, ha, hka⟩ := exists_of_mem_comp ha'
      obtain ⟨b, hb, hkb⟩ := exists_of_mem_comp hb'
      have hpair : (key k a', key k b') ∈ P := by
        refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · rw [← hka]; exact mem_image_of_mem _ ha
        · rw [← hkb]; exact mem_image_of_mem _ hb
        · rw [← key_add]; exact hzy
      have hle := hmax _ hpair
      simp only [fcard_key] at hle
      rw [mem_image]
      refine ⟨((a' + b') k).toNat, ?_, ?_⟩
      · rw [mem_range]
        simp only [Pi.add_apply]
        omega
      · rw [← hzy, Int.toNat_of_nonneg (by simp only [Pi.add_apply]; omega)]
        exact update_key k _
    calc _ ≤ #((range (fcard k A p.1 + fcard k B p.2 - 1)).image
          (fun t : ℕ => Function.update y k (t : ℤ))) := card_le_card hsub
      _ ≤ #(range (fcard k A p.1 + fcard k B p.2 - 1)) := card_image_le
      _ = _ := card_range _
  -- Claim 2: Cauchy--Davenport on the `k`-th coordinates
  have h2 : fcard k A p.1 + fcard k B p.2 - 1 ≤ #((A + B).filter (fun z => key k z = y)) := by
    set X := A.filter (fun a => key k a = p.1) with hX
    set Y := B.filter (fun b => key k b = p.2) with hY
    have hfX : fcard k A p.1 = #X := by
      rw [hX, ← hpa, fcard, key_key]
    have hfY : fcard k B p.2 = #Y := by
      rw [hY, ← hpb, fcard, key_key]
    have hXne : X.Nonempty := ⟨a0, mem_filter.mpr ⟨ha0, hpa⟩⟩
    have hYne : Y.Nonempty := ⟨b0, mem_filter.mpr ⟨hb0, hpb⟩⟩
    have hXY : X + Y ⊆ (A + B).filter (fun z => key k z = y) := by
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
      rw [mem_filter] at ha hb ⊢
      exact ⟨mem_add.mpr ⟨a, ha.1, b, hb.1, rfl⟩, by rw [key_add, ha.2, hb.2, hpy]⟩
    let ev : (ℕ → ℤ) →+ ℤ := Pi.evalAddMonoidHom (fun _ => ℤ) k
    have hinj : ∀ (C : Finset (ℕ → ℤ)) (w : ℕ → ℤ), (∀ c ∈ C, key k c = w) →
        Set.InjOn ev ↑C := by
      intro C w hC c hc c' hc' h
      exact eq_of_key_eq ((hC c hc).trans (hC c' hc').symm) h
    have hinjX := hinj X p.1 (fun c hc => (mem_filter.mp hc).2)
    have hinjY := hinj Y p.2 (fun c hc => (mem_filter.mp hc).2)
    have hinjXY := hinj (X + Y) y (fun c hc => by
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hc
      rw [key_add, (mem_filter.mp ha).2, (mem_filter.mp hb).2, hpy])
    have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd (hXne.image ev) (hYne.image ev)
    rw [card_image_of_injOn hinjX, card_image_of_injOn hinjY, ← image_add ev,
      card_image_of_injOn hinjXY] at hcd
    rw [hfX, hfY]
    exact hcd.trans (card_le_card hXY)
  exact h1.trans h2

/-! ### Compressions commute with the shift -/

private lemma key_sh (k : ℕ) (x : ℕ → ℤ) : key (k + 1) (shHom x) = shHom (key k x) := by
  funext i
  rcases i with _ | i
  · simp [key, shHom_zero]
  · simp only [key, shHom_succ, Function.update_apply]
    by_cases h : i = k <;> simp [h]

private lemma fcard_sh (k : ℕ) (A : Finset (ℕ → ℤ)) (w : ℕ → ℤ) :
    fcard (k + 1) (A.image shHom) (shHom w) = fcard k A w := by
  unfold fcard
  rw [filter_image, card_image_of_injective _ shHom_injective]
  congr 1
  ext a
  simp [key_sh, shHom_injective.eq_iff]

private lemma comp_sh (k : ℕ) (A : Finset (ℕ → ℤ)) :
    comp (k + 1) (A.image shHom) = (comp k A).image shHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨h0, hlt⟩ := mem_comp.mp hz
    obtain ⟨b, hb, hkb⟩ := exists_of_mem_comp hz
    obtain ⟨a, -, rfl⟩ := mem_image.mp hb
    have hz0 : z 0 = 0 := by
      have := congrFun hkb 0
      rw [key_sh, shHom_zero, key_apply_of_ne (by omega)] at this
      exact this.symm
    set w : ℕ → ℤ := fun i => z (i + 1) with hw
    have hzw : z = shHom w := by
      funext i
      rcases i with _ | i
      · simp [hz0, shHom_zero]
      · simp [shHom_succ, w]
    rw [hzw] at h0 hlt ⊢
    rw [fcard_sh, shHom_succ] at hlt
    rw [shHom_succ] at h0
    exact mem_image_of_mem _ (mem_comp.mpr ⟨h0, hlt⟩)
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    obtain ⟨h0, hlt⟩ := mem_comp.mp hw
    apply mem_comp.mpr
    rw [fcard_sh, shHom_succ]
    exact ⟨h0, hlt⟩

private lemma comp_eq_self {k : ℕ} {A : Finset (ℕ → ℤ)} (hA : ∀ a ∈ A, a k = 0) : comp k A = A := by
  have hkey : ∀ a ∈ A, key k a = a := fun a ha => by
    rw [key, ← hA a ha, Function.update_eq_self]
  ext z
  rw [mem_comp, fcard]
  have hfil : A.filter (fun a => key k a = key k z) = A.filter (fun a => a = key k z) :=
    filter_congr fun a ha => by rw [hkey a ha]
  rw [hfil]
  have hle : #(A.filter (fun a => a = key k z)) ≤ 1 :=
    card_le_one.mpr fun a ha b hb => (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
  constructor
  · rintro ⟨h0, hlt⟩
    have hpos : 0 < #(A.filter (fun a => a = key k z)) := by omega
    obtain ⟨a, ha⟩ := card_pos.mp hpos
    rw [mem_filter] at ha
    have hz : z k = 0 := by omega
    have : key k z = z := by rw [key, ← hz, Function.update_eq_self]
    rw [← this, ← ha.2]
    exact ha.1
  · intro hz
    have hk : z k = 0 := hA z hz
    have : key k z = z := by rw [key, ← hk, Function.update_eq_self]
    have hpos : 0 < #(A.filter (fun a => a = key k z)) :=
      card_pos.mpr ⟨z, mem_filter.mpr ⟨hz, this.symm⟩⟩
    omega

/-! ### Compressed sets -/

/-- `A` is compressed in direction `k`: its `k`-th coordinates are nonnegative and it is closed
under lowering a positive `k`-th coordinate by one. -/
private def IsComp (k : ℕ) (A : Finset (ℕ → ℤ)) : Prop :=
  ∀ z ∈ A, 0 ≤ z k ∧ (1 ≤ z k → Function.update z k (z k - 1) ∈ A)

private lemma isComp_comp (k : ℕ) (A : Finset (ℕ → ℤ)) : IsComp k (comp k A) := by
  intro z hz
  obtain ⟨h0, hlt⟩ := mem_comp.mp hz
  refine ⟨h0, fun h1 => mem_comp.mpr ?_⟩
  rw [fcard_update, Function.update_self]
  omega

private lemma isComp_comp_of_ne {j k : ℕ} (hjk : j ≠ k) {A : Finset (ℕ → ℤ)} (hA : IsComp j A) :
    IsComp j (comp k A) := by
  intro z hz
  obtain ⟨a, ha, hka⟩ := exists_of_mem_comp hz
  have hza : z j = a j := by
    rw [← key_apply_of_ne hjk z, ← hka, key_apply_of_ne hjk]
  refine ⟨hza ▸ (hA a ha).1, fun h1 => ?_⟩
  obtain ⟨h0, hlt⟩ := mem_comp.mp hz
  apply mem_comp.mpr
  rw [Function.update_of_ne (Ne.symm hjk)]
  refine ⟨h0, lt_of_lt_of_le hlt ?_⟩
  -- injection from the fiber through `z` to the fiber through the decremented point
  unfold fcard
  have : #(A.filter (fun a => key k a = key k z)) ≤
      #(A.filter (fun a => key k a = key k (Function.update z j (z j - 1)))) := by
    refine card_le_card_of_injOn (fun a => Function.update a j (a j - 1)) ?_ ?_
    · intro c hc
      rw [coe_filter] at hc ⊢
      obtain ⟨hcA, hck⟩ := hc
      have hcj : c j = z j := by
        rw [← key_apply_of_ne hjk c, hck, key_apply_of_ne hjk]
      refine ⟨(hA c hcA).2 (by omega), ?_⟩
      funext i
      by_cases hik : i = k
      · subst hik; simp [key]
      · by_cases hij : i = j
        · subst hij
          simp [key_apply_of_ne hik, hcj]
        · simp only [key_apply_of_ne hik, Function.update_of_ne hij]
          rw [← key_apply_of_ne hik c, hck, key_apply_of_ne hik]
    · intro c hc c' hc' h
      have hcj : c j = c' j := by
        rw [coe_filter] at hc hc'
        rw [← key_apply_of_ne hjk c, hc.2, ← hc'.2, key_apply_of_ne hjk]
      funext i
      have := congrFun h i
      by_cases hij : i = j
      · subst hij; exact hcj
      · simpa [Function.update_of_ne hij] using this
  exact_mod_cast this

/-! ### Supports and sweeps of compressions -/

/-- Every point of `A` vanishes at the coordinates `i ≥ D`. -/
private def Supp (D : ℕ) (A : Finset (ℕ → ℤ)) : Prop := ∀ x ∈ A, ∀ i, D ≤ i → x i = 0

private lemma supp_comp {D k : ℕ} {A : Finset (ℕ → ℤ)} (hA : Supp D A) (hk : k < D) :
    Supp D (comp k A) := by
  intro z hz i hi
  obtain ⟨a, ha, hka⟩ := exists_of_mem_comp hz
  have hik : i ≠ k := by omega
  rw [← key_apply_of_ne hik z, ← hka, key_apply_of_ne hik]
  exact hA a ha i hi

/-- `sweep j m A` compresses `A` in the directions `j + m - 1, …, j + 1, j`, in this order. -/
private def sweep : ℕ → ℕ → Finset (ℕ → ℤ) → Finset (ℕ → ℤ)
  | _, 0, A => A
  | j, m + 1, A => comp j (sweep (j + 1) m A)

private lemma card_sweep (j m : ℕ) (A : Finset (ℕ → ℤ)) : #(sweep j m A) = #A := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih => simp [sweep, card_comp, ih]

private lemma card_sweep_add_sweep_le (j m : ℕ) (A B : Finset (ℕ → ℤ)) :
    #(sweep j m A + sweep j m B) ≤ #(A + B) := by
  induction m generalizing j with
  | zero => exact le_rfl
  | succ m ih => exact (card_comp_add_comp_le _ _ _).trans (ih (j + 1))

private lemma sweep_sh (j m : ℕ) (A : Finset (ℕ → ℤ)) :
    sweep (j + 1) m (A.image shHom) = (sweep j m A).image shHom := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih =>
    simp only [sweep]
    rw [ih (j + 1), comp_sh]

private lemma sweep_succ' (j m : ℕ) (A : Finset (ℕ → ℤ)) :
    sweep j (m + 1) A = sweep j m (comp (j + m) A) := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih =>
    have h := ih (j + 1)
    rw [show j + 1 + m = j + (m + 1) by omega] at h
    change comp j (sweep (j + 1) (m + 1) A) = comp j (sweep (j + 1) m (comp (j + (m + 1)) A))
    rw [h]

private lemma isComp_sweep (j m : ℕ) (A : Finset (ℕ → ℤ)) (i : ℕ) (hi1 : j ≤ i) (hi2 : i < j + m) :
    IsComp i (sweep j m A) := by
  induction m generalizing j with
  | zero => omega
  | succ m ih =>
    simp only [sweep]
    by_cases hij : i = j
    · subst hij; exact isComp_comp _ _
    · exact isComp_comp_of_ne hij (ih (j + 1) (by omega) (by omega))

private lemma supp_sweep {D : ℕ} (j m : ℕ) (A : Finset (ℕ → ℤ)) (hA : Supp D A) (hjm : j + m ≤ D) :
    Supp D (sweep j m A) := by
  induction m generalizing j with
  | zero => exact hA
  | succ m ih => exact supp_comp (ih (j + 1) (by omega)) (by omega)

/-! ### Down-sets -/

/-- `S` is a down-set of the nonnegative orthant. -/
private def IsDown (S : Finset (ℕ → ℤ)) : Prop :=
  (∀ x ∈ S, 0 ≤ x) ∧ ∀ x ∈ S, ∀ y : ℕ → ℤ, 0 ≤ y → y ≤ x → y ∈ S

private lemma isDown_of_isComp {D : ℕ} {S : Finset (ℕ → ℤ)} (hc : ∀ i, i < D → IsComp i S)
    (hs : Supp D S) : IsDown S := by
  have hnn : ∀ x ∈ S, 0 ≤ x := by
    intro x hx i
    by_cases hi : i < D
    · exact (hc i hi x hx).1
    · rw [hs x hx i (by omega)]; rfl
  refine ⟨hnn, ?_⟩
  suffices H : ∀ n : ℕ, ∀ x ∈ S, ∀ y : ℕ → ℤ, 0 ≤ y → y ≤ x →
      ∑ i ∈ range D, (x i - y i).toNat = n → y ∈ S by
    intro x hx y hy hyx
    exact H _ x hx y hy hyx rfl
  intro n
  induction n with
  | zero =>
    intro x hx y hy hyx hsum
    have : y = x := by
      funext i
      have h2 : 0 ≤ y i := by simpa using hy i
      have h3 : y i ≤ x i := hyx i
      by_cases hi : i < D
      · have := (sum_eq_zero_iff.mp hsum) i (mem_range.mpr hi)
        omega
      · have h1 := hs x hx i (by omega)
        omega
    rw [this]; exact hx
  | succ n ih =>
    intro x hx y hy hyx hsum
    obtain ⟨i, hi, hlt⟩ : ∃ i ∈ range D, y i < x i := by
      by_contra hcon
      push Not at hcon
      have : ∑ i ∈ range D, (x i - y i).toNat = 0 :=
        sum_eq_zero fun i hi => by have := hcon i hi; omega
      omega
    have hyi := hy i
    simp only [Pi.zero_apply] at hyi
    have hx' : Function.update x i (x i - 1) ∈ S := (hc i (mem_range.mp hi) x hx).2 (by omega)
    apply ih _ hx' y hy
    · intro j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; omega
      · rw [Function.update_of_ne hj]; exact hyx j
    · rw [← Finset.add_sum_erase _ _ hi] at hsum
      rw [← Finset.add_sum_erase _ _ hi]
      have : ∀ j ∈ (range D).erase i,
          (Function.update x i (x i - 1) j - y j).toNat = (x j - y j).toNat := by
        intro j hj
        rw [Function.update_of_ne (ne_of_mem_erase hj)]
      rw [sum_congr rfl this, Function.update_self]
      omega

private lemma sh_nonneg {b : ℕ → ℤ} (hb : 0 ≤ b) : 0 ≤ shHom b := by
  intro i
  rcases i with _ | i
  · simp [shHom_zero]
  · rw [shHom_succ]; exact hb i

private lemma isDown_add_sh {A : Finset (ℕ → ℤ)} (hA : IsDown A) : IsDown (A + A.image shHom) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨a, ha, b', hb', rfl⟩ := mem_add.mp hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hb'
    exact add_nonneg (hA.1 a ha) (sh_nonneg (hA.1 b hb))
  · intro z hz w hw hwz
    obtain ⟨a, ha, b', hb', rfl⟩ := mem_add.mp hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hb'
    have hwi : ∀ i, 0 ≤ w i := fun i => by simpa using hw i
    have hai : ∀ i, 0 ≤ a i := fun i => by simpa using hA.1 a ha i
    have hbi : ∀ i, 0 ≤ b i := fun i => by simpa using hA.1 b hb i
    have hwz0 : w 0 ≤ a 0 := by simpa [shHom_zero] using hwz 0
    have hwzs : ∀ i, w (i + 1) ≤ a (i + 1) + b i := fun i => by simpa [shHom_succ] using hwz (i + 1)
    set a' : ℕ → ℤ := fun i => min (w i) (a i) with ha'def
    set b'' : ℕ → ℤ := fun i => w (i + 1) - min (w (i + 1)) (a (i + 1)) with hb''def
    have ha'0 : 0 ≤ a' := fun i => by
      have := hwi i
      have := hai i
      simp only [Pi.zero_apply, a']
      omega
    have ha'le : a' ≤ a := fun i => by simp only [a']; omega
    have hb''0 : 0 ≤ b'' := fun i => by simp only [Pi.zero_apply, b'']; omega
    have hb''le : b'' ≤ b := fun i => by
      have := hwzs i
      have := hbi i
      simp only [b'']
      omega
    have ha' : a' ∈ A := hA.2 a ha a' ha'0 ha'le
    have hb'' : b'' ∈ A := hA.2 b hb b'' hb''0 hb''le
    have hw' : w = a' + shHom b'' := by
      funext i
      rcases i with _ | i
      · simp only [Pi.add_apply, shHom_zero, a']; omega
      · simp only [Pi.add_apply, shHom_succ, a', b'']; omega
    rw [hw']
    exact add_mem_add ha' (mem_image_of_mem _ hb'')

/-! ### Projections onto coordinate sets -/

open Classical in
/-- The points of `S` supported in the set `J` of coordinates. -/
private def sub (S : Finset (ℕ → ℤ)) (J : Finset ℕ) : Finset (ℕ → ℤ) :=
  S.filter (fun x => ∀ i, i ∉ J → x i = 0)

/-- The projection that keeps the coordinates in `J` and sets the others to `0`. -/
private def proj (J : Finset ℕ) (x : ℕ → ℤ) : ℕ → ℤ := fun i => if i ∈ J then x i else 0

private lemma proj_mem {S : Finset (ℕ → ℤ)} (hS : IsDown S) {x : ℕ → ℤ} (hx : x ∈ S)
    (J : Finset ℕ) :
    proj J x ∈ S := by
  refine hS.2 x hx _ (fun i => ?_) (fun i => ?_)
  · have : 0 ≤ x i := by simpa using hS.1 x hx i
    by_cases hi : i ∈ J <;> simp [proj, hi, this]
  · by_cases hi : i ∈ J
    · simp [proj, hi]
    · simpa [proj, hi] using hS.1 x hx i

private lemma sh_eq_zero_of_mem_sub {S : Finset (ℕ → ℤ)} {J : Finset ℕ} {y : ℕ → ℤ}
    (hy : y ∈ sub S J)
    {i : ℕ} (hi : i ∉ J.image Nat.succ) : shHom y i = 0 := by
  classical
  rcases i with _ | i
  · exact shHom_zero y
  · rw [shHom_succ]
    refine (mem_filter.mp hy).2 i fun hiJ => hi ?_
    exact mem_image.mpr ⟨i, hiJ, rfl⟩

private lemma noplane_step {S : Finset (ℕ → ℤ)} (hS : IsDown S) (J1 J2 : Finset ℕ) :
    #(sub S J1) * #(sub S J2) ≤
      #(S + S.image shHom) * #(sub S (J1 ∩ J2.image Nat.succ)) := by
  classical
  rw [← card_product, ← card_product]
  refine card_le_card_of_injOn
    (fun p => (p.1 + shHom p.2, proj (J1 ∩ J2.image Nat.succ) p.1)) ?_ ?_
  · intro p hp
    rw [mem_coe, mem_product] at hp ⊢
    obtain ⟨hx, hy⟩ := hp
    have hx' := mem_filter.mp hx
    have hy' := mem_filter.mp hy
    refine ⟨add_mem_add hx'.1 (mem_image_of_mem _ hy'.1), mem_filter.mpr ⟨proj_mem hS hx'.1 _, ?_⟩⟩
    intro i hi
    simp [proj, hi]
  · intro p hp q hq hpq
    rw [mem_coe, mem_product] at hp hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨hsum, hproj⟩ := hpq
    have hx : p.1 = q.1 := by
      funext i
      by_cases hi1 : i ∈ J1
      · by_cases hi2 : i ∈ J2.image Nat.succ
        · have := congrFun hproj i
          simpa [proj, hi1, hi2] using this
        · have := congrFun hsum i
          simp only [Pi.add_apply] at this
          rwa [sh_eq_zero_of_mem_sub hp.2 hi2, sh_eq_zero_of_mem_sub hq.2 hi2, add_zero,
            add_zero] at this
      · rw [(mem_filter.mp hp.1).2 i hi1, (mem_filter.mp hq.1).2 i hi1]
    have hy : p.2 = q.2 := by
      apply shHom_injective
      rw [hx] at hsum
      exact add_left_cancel hsum
    exact Prod.ext hx hy

/-- The elements `j ∈ I` with `j, j - 1, …, j - s ∈ I`. -/
private def runs (I : Finset ℕ) (s : ℕ) : Finset ℕ := I.filter (fun j => ∀ t ≤ s, t ≤ j ∧ j - t ∈ I)

private lemma runs_zero (I : Finset ℕ) : runs I 0 = I := by
  ext j
  simp only [runs, mem_filter]
  constructor
  · exact fun h => h.1
  · intro hj
    refine ⟨hj, fun t ht => ?_⟩
    have : t = 0 := by omega
    subst this
    simpa using hj

private lemma runs_succ (I : Finset ℕ) (s : ℕ) :
    I ∩ (runs I s).image Nat.succ = runs I (s + 1) := by
  ext j
  simp only [mem_inter, mem_image, runs, mem_filter]
  constructor
  · rintro ⟨hjI, j', ⟨hj'I, hj'⟩, rfl⟩
    refine ⟨hjI, fun t ht => ?_⟩
    rcases t with _ | t
    · simpa using hjI
    · obtain ⟨h1, h2⟩ := hj' t (by omega)
      exact ⟨by omega, by simpa [Nat.succ_sub_succ] using h2⟩
  · rintro ⟨hjI, h⟩
    obtain ⟨h1, h2⟩ := h 1 (by omega)
    refine ⟨hjI, j - 1, ⟨h2, fun t ht => ?_⟩, by omega⟩
    obtain ⟨h3, h4⟩ := h (t + 1) (by omega)
    exact ⟨by omega, by rw [show j - 1 - t = j - (t + 1) by omega]; exact h4⟩

private lemma noplane_pow {S : Finset (ℕ → ℤ)} (hS : IsDown S) (I : Finset ℕ) (s : ℕ) :
    #(sub S I) ^ (s + 1) ≤ #(S + S.image shHom) ^ s * #(sub S (runs I s)) := by
  induction s with
  | zero => simp [runs_zero]
  | succ s ih =>
    calc #(sub S I) ^ (s + 1 + 1) = #(sub S I) * #(sub S I) ^ (s + 1) := by ring
      _ ≤ #(sub S I) * (#(S + S.image shHom) ^ s * #(sub S (runs I s))) :=
          Nat.mul_le_mul_left _ ih
      _ = #(S + S.image shHom) ^ s * (#(sub S I) * #(sub S (runs I s))) := by ring
      _ ≤ #(S + S.image shHom) ^ s *
            (#(S + S.image shHom) * #(sub S (I ∩ (runs I s).image Nat.succ))) :=
          Nat.mul_le_mul_left _ (noplane_step hS I (runs I s))
      _ = #(S + S.image shHom) ^ (s + 1) * #(sub S (runs I (s + 1))) := by
          rw [runs_succ]; ring

private lemma card_sub_empty_le (S : Finset (ℕ → ℤ)) : #(sub S ∅) ≤ 1 := by
  classical
  refine card_le_one.mpr fun a ha b hb => ?_
  funext i
  rw [(mem_filter.mp ha).2 i (notMem_empty i), (mem_filter.mp hb).2 i (notMem_empty i)]

/-- The projection bound of Conlon and Lim: if `I` contains no `L` consecutive integers, then
`|S_I|^L ≤ |S + Φ S|^(L - 1)` for a down-set `S`. -/
private lemma noplane {S : Finset (ℕ → ℤ)} (hS : IsDown S) (I : Finset ℕ) (L : ℕ) (hL : 1 ≤ L)
    (hI : runs I (L - 1) = ∅) :
    #(sub S I) ^ L ≤ #(S + S.image shHom) ^ (L - 1) := by
  have h := noplane_pow hS I (L - 1)
  rw [hI, Nat.sub_add_cancel hL] at h
  calc #(sub S I) ^ L ≤ #(S + S.image shHom) ^ (L - 1) * #(sub S ∅) := h
    _ ≤ #(S + S.image shHom) ^ (L - 1) * 1 := Nat.mul_le_mul_left _ (card_sub_empty_le S)
    _ = _ := mul_one _

/-! ### Adding the cube `{0, 1}^D` to a down-set -/

/-- The indicator vector of a finite set of coordinates. -/
private def ind (J : Finset ℕ) : ℕ → ℤ := fun i => if i ∈ J then 1 else 0

/-- The vertices of the unit cube `{0, 1}^D`, as indicator vectors. -/
private def cube (D : ℕ) : Finset (ℕ → ℤ) := (range D).powerset.image ind

private lemma ind_apply (J : Finset ℕ) (i : ℕ) : ind J i = if i ∈ J then 1 else 0 := rfl

private lemma ind_cases (J : Finset ℕ) (i : ℕ) : (i ∈ J ∧ ind J i = 1) ∨ (i ∉ J ∧ ind J i = 0) := by
  by_cases h : i ∈ J <;> simp [ind, h]

private lemma card_add_cube_le {S : Finset (ℕ → ℤ)} {D : ℕ} (hS : IsDown S) (hs : Supp D S) :
    #(S + cube D) ≤ ∑ J ∈ (range D).powerset, #(sub S J) := by
  classical
  rw [← card_sigma]
  refine card_le_card_of_injOn (fun y => ⟨(range D).filter (fun i => y i ≠ 0),
      y - ind ((range D).filter (fun i => y i ≠ 0))⟩) ?_ ?_
  · intro y hy
    rw [mem_coe] at hy
    obtain ⟨s, hsS, c, hc, rfl⟩ := mem_add.mp hy
    obtain ⟨J0, hJ0, rfl⟩ := mem_image.mp hc
    rw [mem_powerset] at hJ0
    rw [mem_coe, mem_sigma]
    dsimp only
    refine ⟨mem_powerset.mpr (filter_subset _ _), ?_⟩
    have hsi : ∀ i, 0 ≤ s i := fun i => by simpa using hS.1 s hsS i
    have hJ0D : ∀ i, D ≤ i → i ∉ J0 := fun i hi hiJ => by
      have := mem_range.mp (hJ0 hiJ); omega
    -- the pointwise description of the new point
    have hpt : ∀ i, (s + ind J0 - ind ((range D).filter (fun j => (s + ind J0) j ≠ 0))) i =
        if i < D ∧ s i + ind J0 i ≠ 0 then s i + ind J0 i - 1 else s i + ind J0 i := by
      intro i
      simp only [Pi.sub_apply, Pi.add_apply, ind_apply (filter _ _), mem_filter, mem_range]
      split_ifs <;> ring
    rw [sub, mem_filter]
    constructor
    · apply hS.2 s hsS
      · intro i
        have h1 := hsi i
        rw [Pi.zero_apply, hpt]
        beta_reduce
        rcases ind_cases J0 i with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> split_ifs with hh
        · omega
        · omega
        · obtain ⟨_, hh2⟩ := hh; omega
        · omega
      · intro i
        have h1 := hsi i
        rw [hpt]
        beta_reduce
        rcases ind_cases J0 i with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> split_ifs with hh
        · omega
        · simp only [not_and_or, not_lt, ne_eq, not_not] at hh
          rcases hh with hh | hh
          · exact absurd (mem_range.mp (hJ0 ‹i ∈ J0›)) (by omega)
          · omega
        · omega
        · omega
    · intro i hi
      simp only [mem_filter, mem_range, not_and, not_not, Pi.add_apply] at hi
      rw [hpt]
      by_cases hiD : i < D
      · have := hi hiD
        rw [ite_eq_right (fun hh => hh.2 this)]
        exact this
      · have h1 := hs s hsS i (by omega)
        have h2 : ind J0 i = 0 := by
          rcases ind_cases J0 i with ⟨hiJ, _⟩ | ⟨_, h2⟩
          · exact absurd hiJ (hJ0D i (by omega))
          · exact h2
        rw [h1, h2, ite_eq_right (fun hh => hiD hh.1)]
        rfl
  · intro y _ y' _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' := eq_of_heq h2
    calc y = (y - ind ((range D).filter (fun i => y i ≠ 0))) +
          ind ((range D).filter (fun i => y i ≠ 0)) := (sub_add_cancel _ _).symm
      _ = (y' - ind ((range D).filter (fun i => y' i ≠ 0))) +
          ind ((range D).filter (fun i => y' i ≠ 0)) := by rw [h2', h1]
      _ = y' := sub_add_cancel _ _

/-! ### Counting coordinate sets with a long run -/

private lemma card_superset_le (R T : Finset ℕ) (hT : T ⊆ R) :
    #(R.powerset.filter (fun J => T ⊆ J)) ≤ 2 ^ (#R - #T) := by
  calc #(R.powerset.filter (fun J => T ⊆ J)) ≤ #((R \ T).powerset) := by
        refine card_le_card_of_injOn (fun J => J \ T) ?_ ?_
        · intro J hJ
          rw [mem_coe, mem_filter, mem_powerset] at hJ
          rw [mem_coe, mem_powerset]
          exact sdiff_subset_sdiff hJ.1 le_rfl
        · intro J hJ J' hJ' h
          rw [mem_coe, mem_filter] at hJ hJ'
          simp only at h
          rw [← sdiff_union_of_subset hJ.2, ← sdiff_union_of_subset hJ'.2, h]
    _ = 2 ^ (#R - #T) := by rw [card_powerset, card_sdiff_of_subset hT]

private lemma card_bad_le (D L : ℕ) (hL : 1 ≤ L) (W : Finset ℕ) :
    #((range D).powerset.filter (fun J => (runs (J ∩ W) (L - 1)).Nonempty)) ≤
      #W * 2 ^ (D - L) := by
  have hsub : (range D).powerset.filter (fun J => (runs (J ∩ W) (L - 1)).Nonempty) ⊆
      (W.filter (fun j => L - 1 ≤ j)).biUnion
        (fun j => (range D).powerset.filter (fun J => Ico (j + 1 - L) (j + 1) ⊆ J)) := by
    intro J hJ
    rw [mem_filter] at hJ
    obtain ⟨hJD, j, hj⟩ := hJ
    rw [runs, mem_filter, mem_inter] at hj
    have hLj := (hj.2 (L - 1) le_rfl).1
    rw [mem_biUnion]
    refine ⟨j, mem_filter.mpr ⟨hj.1.2, hLj⟩, mem_filter.mpr ⟨hJD, ?_⟩⟩
    intro i hi
    rw [mem_Ico] at hi
    have := (hj.2 (j - i) (by omega)).2
    rw [mem_inter, show j - (j - i) = i by omega] at this
    exact this.1
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ j ∈ W.filter (fun j => L - 1 ≤ j),
          #((range D).powerset.filter (fun J => Ico (j + 1 - L) (j + 1) ⊆ J)) :=
        card_biUnion_le
    _ ≤ ∑ j ∈ W.filter (fun j => L - 1 ≤ j), 2 ^ (D - L) := by
        refine sum_le_sum fun j hj => ?_
        have hLj := (mem_filter.mp hj).2
        by_cases hT : Ico (j + 1 - L) (j + 1) ⊆ range D
        · calc _ ≤ 2 ^ (#(range D) - #(Ico (j + 1 - L) (j + 1))) := card_superset_le _ _ hT
            _ = 2 ^ (D - L) := by
                rw [card_range, Nat.card_Ico, show j + 1 - (j + 1 - L) = L by omega]
        · have : (range D).powerset.filter (fun J => Ico (j + 1 - L) (j + 1) ⊆ J) = ∅ := by
            ext J
            simp only [mem_filter, mem_powerset, notMem_empty, iff_false, not_and]
            exact fun hJ hT' => hT (hT'.trans hJ)
          rw [this, card_empty]
          exact Nat.zero_le _
    _ = #(W.filter (fun j => L - 1 ≤ j)) * 2 ^ (D - L) := by rw [sum_const, smul_eq_mul]
    _ ≤ #W * 2 ^ (D - L) := Nat.mul_le_mul_right _ (card_filter_le _ _)

/-! ### The discrete Brunn–Minkowski inequality -/

/-- The point of `ℝ^D` given by the first `D` coordinates of a lattice point. -/
private def emb (D : ℕ) (x : ℕ → ℤ) : Fin D → ℝ := fun i => (x i : ℝ)

/-- The union of the closed unit cubes at the points of `Z`. -/
private def boxSet (D : ℕ) (Z : Finset (ℕ → ℤ)) : Set (Fin D → ℝ) :=
  ⋃ z ∈ Z, Set.Icc (emb D z) (emb D z + 1)

private lemma isCompact_boxSet (D : ℕ) (Z : Finset (ℕ → ℤ)) : IsCompact (boxSet D Z) :=
  isCompact_biUnion _ fun _ _ => isCompact_Icc

private lemma measurableSet_boxSet (D : ℕ) (Z : Finset (ℕ → ℤ)) : MeasurableSet (boxSet D Z) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Icc

private lemma volume_boxSet_le (D : ℕ) (Z : Finset (ℕ → ℤ)) : volume (boxSet D Z) ≤ #Z := by
  calc volume (boxSet D Z) ≤ ∑ z ∈ Z, volume (Set.Icc (emb D z) (emb D z + 1)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _z ∈ Z, (1 : ℝ≥0∞) := by
        refine sum_congr rfl fun z _ => ?_
        rw [Real.volume_Icc_pi]
        simp
    _ = #Z := by simp

private lemma le_volume_boxSet (D : ℕ) (Z : Finset (ℕ → ℤ)) (hZ : Supp D Z) :
    (#Z : ℝ≥0∞) ≤ volume (boxSet D Z) := by
  have hsub : (⋃ z ∈ Z, Set.univ.pi (fun i => Set.Ico (emb D z i) (emb D z i + 1))) ⊆
      boxSet D Z := by
    refine Set.iUnion₂_mono fun z _ => ?_
    intro p hp
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ico, true_implies] at hp
    exact ⟨fun i => (hp i).1, fun i => (hp i).2.le⟩
  have hdisj : (↑Z : Set (ℕ → ℤ)).PairwiseDisjoint
      (fun z => Set.univ.pi (fun i => Set.Ico (emb D z i) (emb D z i + 1))) := by
    intro z hz z' hz' hne
    rw [Function.onFun, Set.disjoint_left]
    intro p hp hp'
    apply hne
    funext j
    by_cases hj : j < D
    · simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ico, true_implies] at hp hp'
      have h1 := hp ⟨j, hj⟩
      have h2 := hp' ⟨j, hj⟩
      simp only [emb] at h1 h2
      have h3 : (z j : ℝ) < z' j + 1 := by linarith
      have h4 : (z' j : ℝ) < z j + 1 := by linarith
      have h3' : z j < z' j + 1 := by exact_mod_cast h3
      have h4' : z' j < z j + 1 := by exact_mod_cast h4
      omega
    · rw [hZ z hz j (by omega), hZ z' hz' j (by omega)]
  have hone : ∀ z : ℕ → ℤ,
      volume (Set.univ.pi (fun i => Set.Ico (emb D z i) (emb D z i + 1))) = 1 := by
    intro z
    rw [Real.volume_pi_Ico]
    simp
  calc (#Z : ℝ≥0∞) = ∑ z ∈ Z,
        volume (Set.univ.pi (fun i => Set.Ico (emb D z i) (emb D z i + 1))) := by
        simp [hone]
    _ = volume (⋃ z ∈ Z, Set.univ.pi (fun i => Set.Ico (emb D z i) (emb D z i + 1))) :=
        (measure_biUnion_finset hdisj fun _ _ =>
          MeasurableSet.univ_pi fun _ => measurableSet_Ico).symm
    _ ≤ volume (boxSet D Z) := measure_mono hsub

private lemma boxSet_add_subset (D : ℕ) (X Y : Finset (ℕ → ℤ)) :
    boxSet D X + boxSet D Y ⊆ boxSet D (X + Y + cube D) := by
  classical
  intro r hr
  obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_add.mp hr
  simp only [boxSet, Set.mem_iUnion] at hp hq ⊢
  obtain ⟨x, hx, hpx⟩ := hp
  obtain ⟨y, hy, hqy⟩ := hq
  set J : Finset ℕ := (range D).filter
    (fun j => ∃ h : j < D, (x j : ℝ) + y j + 1 < p ⟨j, h⟩ + q ⟨j, h⟩) with hJ
  refine ⟨x + y + ind J, add_mem_add (add_mem_add hx hy)
    (mem_image.mpr ⟨J, mem_powerset.mpr (filter_subset _ _), rfl⟩), ?_⟩
  rw [Set.mem_Icc] at hpx hqy ⊢
  constructor
  · intro i
    have h1 := hpx.1 i
    have h2 := hqy.1 i
    have h3 := hpx.2 i
    have h4 := hqy.2 i
    simp only [emb, Pi.add_apply, Pi.one_apply] at h1 h2 h3 h4 ⊢
    by_cases hi : (i : ℕ) ∈ J
    · have hi' := (mem_filter.mp hi).2
      obtain ⟨_, hlt⟩ := hi'
      simp only [ind, hi, ite_true]
      push_cast
      linarith
    · simp only [ind, hi, ite_false]
      push_cast
      linarith
  · intro i
    have h1 := hpx.1 i
    have h2 := hqy.1 i
    have h3 := hpx.2 i
    have h4 := hqy.2 i
    simp only [emb, Pi.add_apply, Pi.one_apply] at h1 h2 h3 h4 ⊢
    by_cases hi : (i : ℕ) ∈ J
    · simp only [ind, hi, ite_true]
      push_cast
      linarith
    · have : ¬ ((x i : ℝ) + y i + 1 < p i + q i) := by
        intro hlt
        exact hi (mem_filter.mpr ⟨mem_range.mpr i.2, i.2, hlt⟩)
      simp only [ind, hi, ite_false]
      push_cast
      linarith

private lemma volume_toLp_image (D : ℕ) (T : Set (Fin D → ℝ)) (hT : MeasurableSet T) :
    volume (WithLp.toLp 2 '' T : Set (EuclideanSpace ℝ (Fin D))) = volume T := by
  have himg : (WithLp.toLp 2 '' T : Set (EuclideanSpace ℝ (Fin D))) = WithLp.ofLp ⁻¹' T := by
    rw [Set.image_eq_preimage_of_inverse (g := WithLp.ofLp) (fun x => WithLp.ofLp_toLp 2 x)
      (fun x => WithLp.toLp_ofLp 2 x)]
  rw [himg]
  exact (PiLp.volume_preserving_ofLp (Fin D)).measure_preimage hT.nullMeasurableSet

/-- The discrete Brunn–Minkowski inequality `|X + Y + {0, 1}^D| ≥ 2^D |X|` for `|X| = |Y|`,
obtained from the Brunn–Minkowski inequality for the unions of unit cubes at `X` and `Y`. -/
private lemma discrete_bm (D : ℕ) (hD : 0 < D) (X Y : Finset (ℕ → ℤ)) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hXs : Supp D X) (hYs : Supp D Y) (hXY : #X = #Y) :
    2 ^ D * #X ≤ #(X + Y + cube D) := by
  set P : Set (EuclideanSpace ℝ (Fin D)) := WithLp.toLp 2 '' boxSet D X with hP
  set Q : Set (EuclideanSpace ℝ (Fin D)) := WithLp.toLp 2 '' boxSet D Y with hQ
  have hcont : Continuous (WithLp.toLp 2 : (Fin D → ℝ) → EuclideanSpace ℝ (Fin D)) :=
    PiLp.continuous_toLp 2 _
  have hPc : IsCompact P := (isCompact_boxSet D X).image hcont
  have hQc : IsCompact Q := (isCompact_boxSet D Y).image hcont
  have hne : ∀ Z : Finset (ℕ → ℤ), Z.Nonempty → (boxSet D Z).Nonempty := by
    rintro Z ⟨z, hz⟩
    refine ⟨emb D z, ?_⟩
    simp only [boxSet, Set.mem_iUnion]
    exact ⟨z, hz, Set.left_mem_Icc.mpr (by intro i; simp)⟩
  have hPne : P.Nonempty := (hne X hX).image _
  have hQne : Q.Nonempty := (hne Y hY).image _
  have hbm := MathlibExt.MeasureTheory.Geometry.BrunnMinkowskiWanted.brunn_minkowski hD
    hPc hPne hQc hQne
  have hPQ : P + Q ⊆ WithLp.toLp 2 '' boxSet D (X + Y + cube D) := by
    rintro r ⟨p, ⟨p', hp', rfl⟩, q, ⟨q', hq', rfl⟩, rfl⟩
    exact ⟨p' + q', boxSet_add_subset D X Y (Set.add_mem_add hp' hq'), WithLp.toLp_add 2 _ _⟩
  have hvP : (#X : ℝ≥0∞) ≤ volume P := by
    rw [hP, volume_toLp_image _ _ (measurableSet_boxSet D X)]; exact le_volume_boxSet D X hXs
  have hvQ : (#X : ℝ≥0∞) ≤ volume Q := by
    rw [hQ, volume_toLp_image _ _ (measurableSet_boxSet D Y), hXY]
    exact le_volume_boxSet D Y hYs
  have hvPQ : volume (P + Q) ≤ #(X + Y + cube D) := by
    calc volume (P + Q) ≤ volume (WithLp.toLp 2 '' boxSet D (X + Y + cube D) :
          Set (EuclideanSpace ℝ (Fin D))) := measure_mono hPQ
      _ = volume (boxSet D (X + Y + cube D)) := volume_toLp_image _ _ (measurableSet_boxSet _ _)
      _ ≤ _ := volume_boxSet_le _ _
  have hpos : (0 : ℝ) ≤ 1 / (D : ℝ) := by positivity
  have key : 2 * (#X : ℝ≥0∞) ^ ((1 : ℝ) / D) ≤ (#(X + Y + cube D) : ℝ≥0∞) ^ ((1 : ℝ) / D) := by
    calc 2 * (#X : ℝ≥0∞) ^ ((1 : ℝ) / D) = (#X : ℝ≥0∞) ^ ((1 : ℝ) / D) +
          (#X : ℝ≥0∞) ^ ((1 : ℝ) / D) := two_mul _
      _ ≤ (volume P) ^ ((1 : ℝ) / D) + (volume Q) ^ ((1 : ℝ) / D) :=
          add_le_add (ENNReal.rpow_le_rpow hvP hpos) (ENNReal.rpow_le_rpow hvQ hpos)
      _ ≤ (volume (P + Q)) ^ ((1 : ℝ) / D) := hbm
      _ ≤ _ := ENNReal.rpow_le_rpow hvPQ hpos
  have key2 := ENNReal.rpow_le_rpow key (by positivity : (0 : ℝ) ≤ D)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    at key2
  have hDD : (1 : ℝ) / D * D = 1 := by field_simp
  rw [hDD, ENNReal.rpow_one, ENNReal.rpow_one, ENNReal.rpow_natCast] at key2
  exact_mod_cast key2


/-! ### Plünnecke–Ruzsa estimates -/

private lemma card_image_sh (A : Finset (ℕ → ℤ)) : #(A.image shHom) = #A :=
  card_image_of_injective _ shHom_injective

private lemma image_sh_add (A B : Finset (ℕ → ℤ)) :
    (A + B).image shHom = A.image shHom + B.image shHom := image_add shHom

private lemma card_le_card_add_sh {A : Finset (ℕ → ℤ)} (hA : A.Nonempty) :
    #A ≤ #(A + A.image shHom) :=
  card_le_card_add_right (hA.image _)

/-- A Plünnecke–Ruzsa estimate: for `S = A + Φ A`, `|S + Φ S| ≤ 81 K^8 |A|` with
`K = |A + Φ A| / |A|`. -/
private lemma card_double_le {A : Finset (ℕ → ℤ)} (hA : A.Nonempty) :
    (#((A + A.image shHom) + (A + A.image shHom).image shHom) : ℝ) ≤
      81 * ((#(A + A.image shHom) : ℝ) / #A) ^ 8 * #A := by
  set X := A.image shHom with hXdef
  set N1 := #(A + X) with hN1
  set n := #A with hn
  have hX : X.Nonempty := hA.image _
  have hXn : #X = n := card_image_sh A
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hA.card_pos
  have hN1n : (n : ℝ) ≤ N1 := by exact_mod_cast card_le_card_add_sh hA
  have hAA : (#(A + A) : ℝ) * n ≤ (N1 : ℝ) ^ 2 := by
    have := ruzsa_triangle_inequality_add_add_add A X A
    rw [hXn, add_comm X A] at this
    rw [sq]
    exact_mod_cast this
  set B' := A ∪ X ∪ X.image shHom with hB'
  have h1 : #(X + B') ≤ #(X + A) + #(X + X) + #(X + X.image shHom) := by
    rw [hB', add_union, add_union]
    exact (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  have hXA : #(X + A) = N1 := by rw [add_comm]
  have hXX : #(X + X) = #(A + A) := by rw [hXdef, ← image_sh_add, card_image_sh]
  have hXXX : #(X + X.image shHom) = N1 := by rw [hXdef, ← image_sh_add, card_image_sh]
  have hXB : (#(X + B') : ℝ) ≤ 3 * (N1 : ℝ) ^ 2 / n := by
    have h1' : (#(X + B') : ℝ) ≤ N1 + #(A + A) + N1 := by
      rw [hXA, hXX, hXXX] at h1
      exact_mod_cast h1
    have hAA' : (#(A + A) : ℝ) ≤ (N1 : ℝ) ^ 2 / n := by
      rw [le_div_iff₀ hnpos]; exact hAA
    have hN1' : (N1 : ℝ) ≤ (N1 : ℝ) ^ 2 / n := by
      rw [le_div_iff₀ hnpos, sq]
      exact mul_le_mul_of_nonneg_left hN1n (by positivity)
    calc (#(X + B') : ℝ) ≤ N1 + #(A + A) + N1 := h1'
      _ ≤ (N1 : ℝ) ^ 2 / n + (N1 : ℝ) ^ 2 / n + (N1 : ℝ) ^ 2 / n := by linarith
      _ = 3 * (N1 : ℝ) ^ 2 / n := by ring
  have hpl := pluennecke_ruzsa_inequality_nsmul_add hX B' 4
  have hpl' : (#(4 • B') : ℝ) ≤ ((#(X + B') : ℝ) / n) ^ 4 * n := by
    have := (NNRat.cast_le (K := ℝ)).mpr hpl
    push_cast at this
    rw [hXn] at this
    exact this
  have hsub : (A + X) + (A + X).image shHom ⊆ 4 • B' := by
    rw [image_sh_add, show (4 : ℕ) • B' = B' + B' + B' + B' by
      rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, add_nsmul, add_nsmul, add_nsmul, one_nsmul]]
    have hA' : A ⊆ B' := fun x hx => mem_union_left _ (mem_union_left _ hx)
    have hX' : X ⊆ B' := fun x hx => mem_union_left _ (mem_union_right _ hx)
    have hXX' : X.image shHom ⊆ B' := fun x hx => mem_union_right _ hx
    rw [← add_assoc]
    exact add_subset_add (add_subset_add (add_subset_add hA' hX') hX') hXX'
  calc (#((A + X) + (A + X).image shHom) : ℝ) ≤ #(4 • B') := by
        exact_mod_cast card_le_card hsub
    _ ≤ ((#(X + B') : ℝ) / n) ^ 4 * n := hpl'
    _ ≤ (3 * (N1 : ℝ) ^ 2 / n / n) ^ 4 * n := by gcongr
    _ = 81 * ((N1 : ℝ) / n) ^ 8 * n := by field_simp; ring

/-! ### The number of coordinates used by a down-set -/

private lemma ind_injective : Function.Injective ind := by
  intro J J' h
  ext i
  have := congrFun h i
  by_cases hi : i ∈ J <;> by_cases hi' : i ∈ J' <;> simp_all [ind]

private lemma ind_insert {J : Finset ℕ} {j : ℕ} (hj : j ∉ J) :
    ind (insert j J) = ind J + ind {j} := by
  funext i
  simp only [ind, Pi.add_apply, mem_insert, mem_singleton]
  by_cases h1 : i = j
  · subst h1; simp [hj]
  · simp [h1]

private lemma ind_mem_nsmul (U : Finset ℕ) (E' : Finset (ℕ → ℤ)) (h0 : (0 : ℕ → ℤ) ∈ E')
    (hE : ∀ u ∈ U, ind {u + 1} ∈ E') :
    ∀ h : ℕ, ∀ T ⊆ U, #T ≤ h → ind (T.image Nat.succ) ∈ h • E' := by
  have hind0 : ind ((∅ : Finset ℕ).image Nat.succ) = 0 := by funext i; simp [ind]
  intro h
  induction h with
  | zero =>
    intro T _ hT
    have : T = ∅ := card_eq_zero.mp (by omega)
    subst this
    rw [zero_nsmul, mem_zero, hind0]
  | succ h ih =>
    intro T hTU hT
    rw [succ_nsmul]
    rcases T.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · have := ih ∅ (empty_subset _) (by simp)
      rw [hind0] at this ⊢
      exact mem_add.mpr ⟨0, this, 0, h0, add_zero 0⟩
    · have hT' := ih (T.erase u) ((erase_subset _ _).trans hTU)
        (by rw [card_erase_of_mem hu]; omega)
      have hnot : u + 1 ∉ (T.erase u).image Nat.succ := by
        intro hmem
        obtain ⟨v, hv, hvu⟩ := mem_image.mp hmem
        exact (ne_of_mem_erase hv) (Nat.succ_injective hvu)
      have heq : ind (T.image Nat.succ) = ind ((T.erase u).image Nat.succ) + ind {u + 1} := by
        conv_lhs => rw [← insert_erase hu]
        rw [image_insert, ind_insert hnot]
      rw [heq]
      exact add_mem_add hT' (hE u (hTU hu))

/-- A down-set `A` using the coordinates in `U` has `|U| ≤ 4 K h` whenever `|A| ≤ 3^h`, where
`K = |A + Φ A| / |A|`: by the Plünnecke–Ruzsa inequality the `h`-fold sums of the shifted unit
vectors number at most `K^h |A|`, and they include the `binom |U| h` sums of `h` distinct ones. -/
private lemma dim_bound {A : Finset (ℕ → ℤ)} (hA : IsDown A) (hne : A.Nonempty)
    (U : Finset ℕ)
    (hU : ∀ u ∈ U, ∃ a ∈ A, a u ≠ 0) (h : ℕ) (hh : 1 ≤ h) (hn : (#A : ℝ) ≤ 3 ^ h) :
    (#U : ℝ) ≤ 4 * ((#(A + A.image shHom) : ℝ) / #A) * h := by
  set n := #A with hn'
  set N1 := #(A + A.image shHom) with hN1
  set K : ℝ := N1 / n with hK
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hne.card_pos
  have hK1 : 1 ≤ K := by
    rw [hK, le_div_iff₀ hnpos, one_mul]
    exact_mod_cast card_le_card_add_sh hne
  set E' : Finset (ℕ → ℤ) := insert 0 (U.image (fun u => ind {u + 1})) with hE'
  have h0A : (0 : ℕ → ℤ) ∈ A := by
    obtain ⟨a, ha⟩ := hne
    exact hA.2 a ha 0 le_rfl (hA.1 a ha)
  have hindA : ∀ u ∈ U, ind {u} ∈ A := by
    intro u hu
    obtain ⟨a, ha, hau⟩ := hU u hu
    refine hA.2 a ha _ ?_ ?_
    · intro i
      by_cases hi : i = u <;> simp [ind, hi]
    · intro i
      have := hA.1 a ha i
      simp only [Pi.zero_apply] at this
      by_cases hi : i = u
      · subst hi; simp only [ind, mem_singleton, ite_eq_left]; omega
      · simp [ind, hi, this]
  have hsh_ind : ∀ u, shHom (ind {u}) = ind {u + 1} := by
    intro u
    funext i
    rcases i with _ | i
    · simp [shHom_zero, ind]
    · simp [shHom_succ, ind]
  have hE'sub : E' ⊆ A.image shHom := by
    intro x hx
    rw [hE', mem_insert, mem_image] at hx
    rcases hx with rfl | ⟨u, hu, rfl⟩
    · exact mem_image.mpr ⟨0, h0A, map_zero shHom⟩
    · exact mem_image.mpr ⟨ind {u}, hindA u hu, hsh_ind u⟩
  have hAE : (#(A + E') : ℝ) ≤ N1 := by exact_mod_cast card_le_card (add_subset_add_left hE'sub)
  have hpl := pluennecke_ruzsa_inequality_nsmul_add hne E' h
  have hpl' : (#(h • E') : ℝ) ≤ K ^ h * n := by
    have := (NNRat.cast_le (K := ℝ)).mpr hpl
    push_cast at this
    calc (#(h • E') : ℝ) ≤ ((#(A + E') : ℝ) / n) ^ h * n := this
      _ ≤ K ^ h * n := by
          gcongr
          rw [hK]
          exact div_le_div_of_nonneg_right hAE hnpos.le
  have hlow : #(U.powersetCard h) ≤ #(h • E') := by
    refine card_le_card_of_injOn (fun T => ind (T.image Nat.succ)) ?_ ?_
    · intro T hT
      rw [mem_coe, mem_powersetCard] at hT
      exact ind_mem_nsmul U E' (mem_insert_self _ _)
        (fun u hu => mem_insert_of_mem (mem_image_of_mem _ hu)) h T hT.1 hT.2.le
    · intro T _ T' _ hTT
      exact image_injective Nat.succ_injective (ind_injective hTT)
  rw [card_powersetCard] at hlow
  set d := #U with hd
  have hch := Nat.pow_le_choose (α := ℝ) h d
  have hfact : (h.factorial : ℝ) ≤ (h : ℝ) ^ h := by exact_mod_cast Nat.factorial_le_pow h
  have hfpos : (0 : ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have h1 : ((d + 1 - h : ℕ) : ℝ) ^ h ≤ (3 * K * h) ^ h := by
    calc ((d + 1 - h : ℕ) : ℝ) ^ h = ((d + 1 - h : ℕ) : ℝ) ^ h / h.factorial * h.factorial := by
          field_simp
      _ ≤ (d.choose h : ℝ) * h.factorial := by gcongr
      _ ≤ (K ^ h * n) * (h : ℝ) ^ h := by
          gcongr
          exact le_trans (by exact_mod_cast hlow) hpl'
      _ ≤ (K ^ h * 3 ^ h) * (h : ℝ) ^ h := by gcongr
      _ = (3 * K * h) ^ h := by ring
  have h2 : ((d + 1 - h : ℕ) : ℝ) ≤ 3 * K * h :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp h1
  have h3 : (d : ℝ) ≤ ((d + 1 - h : ℕ) : ℝ) + h := by
    have : d ≤ (d + 1 - h) + h := by omega
    exact_mod_cast this
  have h4 : (h : ℝ) ≤ K * h := le_mul_of_one_le_left (by positivity) hK1
  linarith

/-! ### The main estimate for down-sets -/

private lemma supp_add {D : ℕ} {A B : Finset (ℕ → ℤ)} (hA : Supp D A) (hB : Supp D B) :
    Supp D (A + B) := by
  intro z hz i hi
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hz
  simp [hA a ha i hi, hB b hb i hi]

private lemma supp_sh {D : ℕ} {A : Finset (ℕ → ℤ)} (hA : Supp D A) :
    Supp (D + 1) (A.image shHom) := by
  intro z hz i hi
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
  rcases i with _ | i
  · omega
  · rw [shHom_succ]; exact hA a ha i (by omega)

private lemma supp_mono {D D' : ℕ} (h : D ≤ D') {A : Finset (ℕ → ℤ)} (hA : Supp D A) : Supp D' A :=
  fun x hx i hi => hA x hx i (by omega)

private lemma sub_eq_sub_inter {S : Finset (ℕ → ℤ)} {W : Finset ℕ}
    (hW : ∀ x ∈ S, ∀ i, i ∉ W → x i = 0) (J : Finset ℕ) : sub S J = sub S (J ∩ W) := by
  classical
  ext x
  simp only [sub, mem_filter, mem_inter, not_and]
  constructor
  · rintro ⟨hx, hJ⟩
    refine ⟨hx, fun i hi => ?_⟩
    by_cases hiJ : i ∈ J
    · exact hW x hx i (hi hiJ)
    · exact hJ i hiJ
  · rintro ⟨hx, hJW⟩
    exact ⟨hx, fun i hi => hJW i (fun h => absurd h hi)⟩

/-- The main estimate for a down-set `A` with `K = |A + Φ A| / |A|`: if `|A| ≤ 3^h` and
`16 K^2 h < 2^L`, then `|A| < (162 K^8)^L`. The sets `J` of coordinates with `L` consecutive
used coordinates contribute little by the dimension bound, the others by the projection bound,
and together they would fall short of the discrete Brunn–Minkowski inequality. -/
private lemma core {A : Finset (ℕ → ℤ)} (hA : IsDown A) (hne : A.Nonempty) {D0 : ℕ}
    (hsupp : Supp D0 A)
    (h L : ℕ) (hh : 1 ≤ h) (hL : 1 ≤ L) (hn3 : (#A : ℝ) ≤ 3 ^ h)
    (hbad : 16 * ((#(A + A.image shHom) : ℝ) / #A) ^ 2 * h < 2 ^ L) :
    (#A : ℝ) < (162 * ((#(A + A.image shHom) : ℝ) / #A) ^ 8) ^ L := by
  classical
  set D1 := max D0 L with hD1
  have hsupp1 : Supp D1 A := supp_mono (le_max_left _ _) hsupp
  set D := D1 + 1 with hD
  have hLD : L ≤ D := by omega
  set n := #A with hn
  set S := A + A.image shHom with hS
  set N1 := #S with hN1
  set K : ℝ := N1 / n with hK
  set M := #(S + S.image shHom) with hM
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hne.card_pos
  have hK1 : 1 ≤ K := by
    rw [hK, le_div_iff₀ hnpos, one_mul]
    exact_mod_cast card_le_card_add_sh hne
  have hSdown : IsDown S := isDown_add_sh hA
  have hSsupp : Supp D S := supp_add (supp_mono (by omega) hsupp1) (supp_sh hsupp1)
  have hM' : (M : ℝ) ≤ 81 * K ^ 8 * n := card_double_le hne
  set U := (range D1).filter (fun i => ∃ a ∈ A, a i ≠ 0) with hU
  have hUb : (#U : ℝ) ≤ 4 * K * h :=
    dim_bound hA hne U (fun u hu => (mem_filter.mp hu).2) h hh hn3
  set W := (range D).filter (fun i => ∃ x ∈ S, x i ≠ 0) with hW
  have hWU : W ⊆ U ∪ U.image Nat.succ := by
    intro i hi
    obtain ⟨_, x, hx, hxi⟩ := mem_filter.mp hi
    obtain ⟨a, ha, b', hb', rfl⟩ := mem_add.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hb'
    by_cases hai : a i = 0
    · rcases i with _ | j
      · simp [hai, shHom_zero] at hxi
      · rw [Pi.add_apply, hai, zero_add, shHom_succ] at hxi
        refine mem_union_right _ (mem_image.mpr ⟨j, mem_filter.mpr ⟨?_, b, hb, hxi⟩, rfl⟩)
        by_contra hj
        exact hxi (hsupp1 b hb j (by simp only [mem_range, not_lt] at hj; omega))
    · refine mem_union_left _ (mem_filter.mpr ⟨?_, a, ha, hai⟩)
      by_contra hi'
      exact hai (hsupp1 a ha i (by simp only [mem_range, not_lt] at hi'; omega))
  have hWb : (#W : ℝ) ≤ 8 * K * h := by
    have h1 : #W ≤ #U + #U := by
      calc #W ≤ #(U ∪ U.image Nat.succ) := card_le_card hWU
        _ ≤ #U + #(U.image Nat.succ) := card_union_le _ _
        _ ≤ #U + #U := Nat.add_le_add_left card_image_le _
    have h2 : (#W : ℝ) ≤ #U + #U := by exact_mod_cast h1
    linarith
  have hWS : ∀ x ∈ S, ∀ i, i ∉ W → x i = 0 := by
    intro x hx i hi
    by_contra hxi
    by_cases hiD : i < D
    · exact hi (mem_filter.mpr ⟨mem_range.mpr hiD, x, hx, hxi⟩)
    · exact hxi (hSsupp x hx i (by omega))
  have hbm : 2 ^ D * n ≤ #(S + cube D) :=
    discrete_bm D (by omega) A (A.image shHom) hne (hne.image _) (supp_mono (by omega) hsupp1)
      (supp_sh hsupp1) (card_image_sh A).symm
  have hcube := card_add_cube_le hSdown hSsupp
  by_contra hcon
  push Not at hcon
  set P := (range D).powerset with hP
  set bad := P.filter (fun J => (runs (J ∩ W) (L - 1)).Nonempty) with hbad'
  set good := P.filter (fun J => ¬ (runs (J ∩ W) (L - 1)).Nonempty) with hgood'
  have hsplit : (∑ J ∈ P, (#(sub S J) : ℝ)) =
      ∑ J ∈ bad, (#(sub S J) : ℝ) + ∑ J ∈ good, (#(sub S J) : ℝ) :=
    (sum_filter_add_sum_filter_not P _ _).symm
  have hgood : ∀ J ∈ good, (#(sub S J) : ℝ) < n / 2 := by
    intro J hJ
    have hJ' := (mem_filter.mp hJ).2
    rw [not_nonempty_iff_eq_empty] at hJ'
    have hnp := noplane hSdown (J ∩ W) L hL hJ'
    rw [← sub_eq_sub_inter hWS J] at hnp
    by_contra hge
    push Not at hge
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hnp
    have h1 : ((n : ℝ) / 2) ^ (L' + 1) ≤ (81 * K ^ 8 * n) ^ L' := by
      calc ((n : ℝ) / 2) ^ (L' + 1) ≤ (#(sub S J) : ℝ) ^ (L' + 1) := by gcongr
        _ ≤ (M : ℝ) ^ L' := by exact_mod_cast hnp
        _ ≤ (81 * K ^ 8 * n) ^ L' := by gcongr
    have h2 : (n : ℝ) ≤ 2 ^ (L' + 1) * (81 * K ^ 8) ^ L' := by
      have hnL : (0 : ℝ) < (n : ℝ) ^ L' := by positivity
      have : (n : ℝ) ^ L' * n ≤ (n : ℝ) ^ L' * (2 ^ (L' + 1) * (81 * K ^ 8) ^ L') := by
        calc (n : ℝ) ^ L' * n = ((n : ℝ) / 2) ^ (L' + 1) * 2 ^ (L' + 1) := by
              rw [div_pow]; field_simp; ring
          _ ≤ (81 * K ^ 8 * n) ^ L' * 2 ^ (L' + 1) := by gcongr
          _ = (n : ℝ) ^ L' * (2 ^ (L' + 1) * (81 * K ^ 8) ^ L') := by ring
      exact le_of_mul_le_mul_left this hnL
    have h3 : (2 : ℝ) ^ (L' + 1) * (81 * K ^ 8) ^ L' < (162 * K ^ 8) ^ (L' + 1) := by
      have hK8 : (1 : ℝ) ≤ K ^ 8 := one_le_pow₀ hK1
      have h81 : (1 : ℝ) < 81 * K ^ 8 := by linarith
      have hpos : (0 : ℝ) < 2 ^ (L' + 1) * (81 * K ^ 8) ^ L' := by positivity
      calc (2 : ℝ) ^ (L' + 1) * (81 * K ^ 8) ^ L' =
            2 ^ (L' + 1) * (81 * K ^ 8) ^ L' * 1 := by ring
        _ < 2 ^ (L' + 1) * (81 * K ^ 8) ^ L' * (81 * K ^ 8) :=
            mul_lt_mul_of_pos_left h81 hpos
        _ = (2 * (81 * K ^ 8)) ^ (L' + 1) := by rw [mul_pow (2 : ℝ)]; ring
        _ = (162 * K ^ 8) ^ (L' + 1) := by congr 1; ring
    linarith
  have hgood_ne : good.Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset _, by simp [runs]⟩⟩
  have hgoodcard : (#good : ℝ) ≤ 2 ^ D := by
    have : #good ≤ #P := card_filter_le _ _
    rw [hP, card_powerset, card_range] at this
    exact_mod_cast this
  have hgoodsum : ∑ J ∈ good, (#(sub S J) : ℝ) < 2 ^ D * ((n : ℝ) / 2) := by
    calc ∑ J ∈ good, (#(sub S J) : ℝ) < ∑ J ∈ good, ((n : ℝ) / 2) :=
          sum_lt_sum_of_nonempty hgood_ne hgood
      _ = #good * ((n : ℝ) / 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ D * ((n : ℝ) / 2) := by gcongr
  have hbadsum : ∑ J ∈ bad, (#(sub S J) : ℝ) ≤ 8 * K * h * 2 ^ (D - L) * N1 := by
    have hbadcard : (#bad : ℝ) ≤ #W * 2 ^ (D - L) := by
      exact_mod_cast card_bad_le D L hL W
    calc ∑ J ∈ bad, (#(sub S J) : ℝ) ≤ ∑ J ∈ bad, (N1 : ℝ) :=
          sum_le_sum fun J _ => by exact_mod_cast card_le_card (filter_subset _ _)
      _ = #bad * (N1 : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (#W * 2 ^ (D - L)) * (N1 : ℝ) := by gcongr
      _ ≤ (8 * K * h * 2 ^ (D - L)) * N1 := by gcongr
  have htot : (2 ^ D * n : ℝ) ≤ ∑ J ∈ bad, (#(sub S J) : ℝ) + ∑ J ∈ good, (#(sub S J) : ℝ) := by
    rw [← hsplit]
    have := hbm.trans hcube
    exact_mod_cast this
  have hN1eq : (N1 : ℝ) = K * n := by rw [hK]; field_simp
  have hpow : (2 : ℝ) ^ (D - L) * 2 ^ L = 2 ^ D := by
    rw [← pow_add, Nat.sub_add_cancel hLD]
  have hfinal : 8 * K * h * 2 ^ (D - L) * N1 < 2 ^ D * ((n : ℝ) / 2) := by
    have hY : (0 : ℝ) < 2 ^ (D - L) * n / 2 := by positivity
    have := mul_lt_mul_of_pos_right hbad hY
    rw [hN1eq, ← hpow]
    calc 8 * K * h * 2 ^ (D - L) * (K * n) = 16 * K ^ 2 * h * (2 ^ (D - L) * n / 2) := by ring
      _ < 2 ^ L * (2 ^ (D - L) * n / 2) := this
      _ = 2 ^ (D - L) * 2 ^ L * ((n : ℝ) / 2) := by ring
  linarith

/-! ### The Krachun–Petrov reduction -/

open Polynomial in
/-- Coefficients of the block encoding `∑ i, X ^ (T * enc i) * c i` of a vector of polynomials of
degree less than `T`. -/
private lemma coeff_block {ι : Type*} [Fintype ι] (enc : ι ≃ Fin (Fintype.card ι)) (T : ℕ)
    (c : ι → ℚ[X]) (hc : ∀ i, (c i).natDegree < T) (i : ι) (j : ℕ) (hj : j < T) :
    (∑ i', X ^ (T * (enc i' : ℕ)) * c i').coeff (T * (enc i : ℕ) + j) = (c i).coeff j := by
  rw [finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_X_pow_mul', ite_eq_left (by omega), show T * (enc i : ℕ) + j - T * (enc i : ℕ) = j by
      omega]
  · intro i' _ hi'
    rw [coeff_X_pow_mul']
    have hne : (enc i' : ℕ) ≠ (enc i : ℕ) := fun h => hi' (enc.injective (Fin.ext h))
    split_ifs with hle
    · rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · apply coeff_eq_zero_of_natDegree_lt
        have h1 := Nat.mul_le_mul_left T (show (enc i' : ℕ) + 1 ≤ enc i by omega)
        have h2 := hc i'
        rw [mul_add, mul_one] at h1
        omega
      · exfalso
        have h1 := Nat.mul_le_mul_left T (show (enc i : ℕ) + 1 ≤ enc i' by omega)
        rw [mul_add, mul_one] at h1
        omega
    · rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

open Polynomial in
/-- The Krachun–Petrov reduction: a finite set of reals and a transcendental `α` give a set `B` of
integer coefficient vectors with `|B| = |A|` and `|B + Φ B| ≤ |A + α • A|`. -/
private lemma kp_reduction (α : ℝ) (hα : Transcendental ℚ α) (A : Finset ℝ) :
    ∃ (B : Finset (ℕ → ℤ)) (D0 : ℕ), #B = #A ∧ Supp D0 B ∧
      #(B + B.image shHom) ≤ #(A + α • A) := by
  classical
  let _ : Algebra ℚ[X] ℝ := (Polynomial.aeval α).toRingHom.toAlgebra
  have hsmul : ∀ (p : ℚ[X]) (r : ℝ), p • r = Polynomial.aeval α p * r := fun p r => rfl
  have hinj : Function.Injective (algebraMap ℚ[X] ℝ) := transcendental_iff_injective.mp hα
  have : Module.IsTorsionFree ℚ[X] ℝ := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  set M := Submodule.span ℚ[X] (A : Set ℝ) with hM
  have : Module.Finite ℚ[X] M := Module.Finite.span_finset _ A
  have : Module.IsTorsionFree ℚ[X] M :=
    Subtype.val_injective.moduleIsTorsionFree _ (fun r m => rfl)
  have : Module.Free ℚ[X] M := Module.free_of_finite_type_torsion_free'
  set ι := Module.Free.ChooseBasisIndex ℚ[X] M
  let bas := Module.Free.chooseBasis ℚ[X] M
  let f : ℝ → (ι → ℚ[X]) := fun r => if h : r ∈ M then (fun i => bas.repr ⟨r, h⟩ i) else 0
  have hf : ∀ r (h : r ∈ M), f r = fun i => bas.repr ⟨r, h⟩ i := fun r h => dite_eq_left h
  have hAM : ∀ a ∈ A, a ∈ M := fun a ha => Submodule.subset_span ha
  have hαM : ∀ r ∈ M, α * r ∈ M := by
    intro r hr
    have := M.smul_mem (X : ℚ[X]) hr
    rwa [hsmul, aeval_X] at this
  have hf_add : ∀ r s, r ∈ M → s ∈ M → f (r + s) = f r + f s := by
    intro r s hr hs
    rw [hf _ (M.add_mem hr hs), hf r hr, hf s hs]
    funext i
    have : (⟨r + s, M.add_mem hr hs⟩ : M) = ⟨r, hr⟩ + ⟨s, hs⟩ := rfl
    rw [this, map_add]
    rfl
  have hf_mul : ∀ r, r ∈ M → f (α * r) = fun i => X * f r i := by
    intro r hr
    rw [hf _ (hαM r hr), hf r hr]
    funext i
    have : (⟨α * r, hαM r hr⟩ : M) = (X : ℚ[X]) • ⟨r, hr⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_smul, hsmul, aeval_X]
    rw [this, map_smul]
    rfl
  have hf_inj : ∀ r s (hr : r ∈ M) (hs : s ∈ M), f r = f s → r = s := by
    intro r s hr hs h
    rw [hf r hr, hf s hs] at h
    have : bas.repr ⟨r, hr⟩ = bas.repr ⟨s, hs⟩ := Finsupp.ext fun i => congrFun h i
    exact congrArg Subtype.val (bas.repr.injective this)
  -- the block encoding into a single polynomial
  let enc : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set T : ℕ := 1 + ∑ a ∈ A, ∑ i, (f a i).natDegree with hT
  have hTdeg : ∀ a ∈ A, ∀ i, (f a i).natDegree < T := by
    intro a ha i
    have h1 : (f a i).natDegree ≤ ∑ i, (f a i).natDegree :=
      Finset.single_le_sum (f := fun i => (f a i).natDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ i, (f a i).natDegree ≤ ∑ a ∈ A, ∑ i, (f a i).natDegree :=
      Finset.single_le_sum (f := fun a => ∑ i, (f a i).natDegree) (fun _ _ => Nat.zero_le _) ha
    omega
  let ψ : (ι → ℚ[X]) → ℚ[X] := fun c => ∑ i, X ^ (T * (enc i : ℕ)) * c i
  have hψ_add : ∀ c d, ψ (c + d) = ψ c + ψ d := by
    intro c d
    simp only [ψ, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hψ_mul : ∀ c, ψ (fun i => X * c i) = X * ψ c := by
    intro c
    simp only [ψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hψ_inj : ∀ a ∈ A, ∀ a' ∈ A, ψ (f a) = ψ (f a') → a = a' := by
    intro a ha a' ha' h
    apply hf_inj a a' (hAM a ha) (hAM a' ha')
    funext i
    ext j
    by_cases hj : j < T
    · rw [← coeff_block enc T (f a) (hTdeg a ha) i j hj,
        ← coeff_block enc T (f a') (hTdeg a' ha') i j hj]
      exact congrArg (fun p : ℚ[X] => p.coeff (T * (enc i : ℕ) + j)) h
    · rw [coeff_eq_zero_of_natDegree_lt (by have := hTdeg a ha i; omega),
        coeff_eq_zero_of_natDegree_lt (by have := hTdeg a' ha' i; omega)]
  -- clearing denominators
  set P : Finset ℚ[X] := A.image (fun a => ψ (f a)) with hP
  set cs : Finset ℚ := P.biUnion (fun p => (range (p.natDegree + 1)).image p.coeff) with hcs
  set Q : ℕ := ∏ q ∈ cs, q.den with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun q _ => q.den_pos
  have hint : ∀ p ∈ P, ∀ j, ∃ z : ℤ, (Q : ℚ) * p.coeff j = z := by
    intro p hp j
    by_cases hj : j ≤ p.natDegree
    · have hmem : p.coeff j ∈ cs :=
        mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨j, mem_range.mpr (by omega), rfl⟩⟩
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hmem
      refine ⟨m * (p.coeff j).num, ?_⟩
      rw [hQ, hm]
      push_cast
      rw [← Rat.mul_den_eq_num]
      ring
    · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp⟩
  let θ : ℚ[X] → (ℕ → ℤ) := fun p j => ⌊(Q : ℚ) * p.coeff j⌋
  have hθ : ∀ p ∈ P, ∀ j, ((θ p j : ℤ) : ℚ) = (Q : ℚ) * p.coeff j := by
    intro p hp j
    obtain ⟨z, hz⟩ := hint p hp j
    simp only [θ, hz, Int.floor_intCast]
  let Θ : ℝ → (ℕ → ℤ) := fun r => θ (ψ (f r))
  have hPmem : ∀ a ∈ A, ψ (f a) ∈ P := fun a ha => mem_image_of_mem _ ha
  set D0 : ℕ := 1 + ∑ p ∈ P, p.natDegree with hD0
  refine ⟨A.image Θ, D0, ?_, ?_, ?_⟩
  · -- injectivity
    refine card_image_of_injOn fun a ha a' ha' h => ?_
    apply hψ_inj a ha a' ha'
    ext j
    have h1 := hθ _ (hPmem a ha) j
    have h2 := hθ _ (hPmem a' ha') j
    have h3 : θ (ψ (f a)) j = θ (ψ (f a')) j := congrFun h j
    have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast hQpos.ne'
    have : (Q : ℚ) * (ψ (f a)).coeff j = (Q : ℚ) * (ψ (f a')).coeff j := by
      rw [← h1, ← h2, h3]
    exact mul_left_cancel₀ hQ0 this
  · -- support
    intro x hx j hj
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    have hdeg : (ψ (f a)).natDegree < j := by
      have := Finset.single_le_sum (f := fun p : ℚ[X] => p.natDegree) (fun _ _ => Nat.zero_le _)
        (hPmem a ha)
      omega
    simp only [Θ, θ, coeff_eq_zero_of_natDegree_lt hdeg, mul_zero, Int.floor_zero]
  · -- the sumset
    have hsub : A.image Θ + (A.image Θ).image shHom ⊆ (A + α • A).image Θ := by
      intro z hz
      obtain ⟨x, hx, y', hy', rfl⟩ := mem_add.mp hz
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hy'
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
      refine mem_image.mpr ⟨a + α * b, mem_add.mpr ⟨a, ha, α * b,
        mem_smul_finset.mpr ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      have hψ : ψ (f (a + α * b)) = ψ (f a) + X * ψ (f b) := by
        rw [hf_add a (α * b) (hAM a ha) (hαM b (hAM b hb)), hψ_add, hf_mul b (hAM b hb),
          hψ_mul]
      funext j
      simp only [Θ, Pi.add_apply]
      rw [hψ]
      rcases j with _ | j
      · rw [shHom_zero, add_zero]
        simp only [θ, coeff_add, coeff_X_mul_zero, add_zero]
      · rw [shHom_succ]
        have e1 := hθ _ (hPmem a ha) (j + 1)
        have e2 := hθ _ (hPmem b hb) j
        simp only [θ] at e1 e2 ⊢
        rw [coeff_add, coeff_X_mul, mul_add, ← e1, ← e2, ← Int.cast_add, Int.floor_intCast]
        simp only [Int.floor_intCast]
    calc #(A.image Θ + (A.image Θ).image shHom) ≤ #((A + α • A).image Θ) := card_le_card hsub
      _ ≤ #(A + α • A) := card_image_le

/-! ### The final estimate -/

private lemma num_ineq (m : ℕ) (hm : 16 ≤ m) : 2 ^ 64 * m ^ 32 ≤ 2 ^ (15 * m) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : 16 ^ 32 * (m + 1) ^ 32 ≤ 17 ^ 32 * m ^ 32 := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left (by omega) 32
    have h2 : (17 : ℕ) ^ 32 ≤ 2 ^ 15 * 16 ^ 32 := by norm_num
    have h3 : (m + 1) ^ 32 ≤ 2 ^ 15 * m ^ 32 := by
      have : 16 ^ 32 * (m + 1) ^ 32 ≤ 16 ^ 32 * (2 ^ 15 * m ^ 32) :=
        calc 16 ^ 32 * (m + 1) ^ 32 ≤ 17 ^ 32 * m ^ 32 := h1
          _ ≤ (2 ^ 15 * 16 ^ 32) * m ^ 32 := Nat.mul_le_mul_right _ h2
          _ = 16 ^ 32 * (2 ^ 15 * m ^ 32) := by ring
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    calc 2 ^ 64 * (m + 1) ^ 32 ≤ 2 ^ 64 * (2 ^ 15 * m ^ 32) := Nat.mul_le_mul_left _ h3
      _ = 2 ^ 15 * (2 ^ 64 * m ^ 32) := by ring
      _ ≤ 2 ^ 15 * 2 ^ (15 * m) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (15 * (m + 1)) := by rw [← pow_add]; ring_nf

private lemma exp_ineq (m : ℕ) (hm : 16 ≤ m) : (32 + m) * m ≤ 4 * (m - 1) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 16 := ⟨m - 16, by omega⟩
  rw [show k + 16 - 1 = k + 15 by omega]
  nlinarith

/-- The real-variable part of the final estimate. -/
private lemma final_num (n : ℕ) (K : ℝ) (hn : 1 ≤ n) (hK1 : 1 ≤ K)
    (hP : ∀ h L : ℕ, 1 ≤ h → 1 ≤ L → (n : ℝ) ≤ 3 ^ h → 16 * K ^ 2 * h < 2 ^ L →
      (n : ℝ) < (162 * K ^ 8) ^ L)
    (ht : 16 < Real.sqrt (Real.log n)) :
    Real.exp (Real.log 2 / 32 * Real.sqrt (Real.log n)) ≤ K := by
  by_contra hcon
  push Not at hcon
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨t, htdef⟩ : ∃ t, t = Real.sqrt (Real.log n) := ⟨_, rfl⟩
  rw [← htdef] at ht hcon
  have ht0 : 0 ≤ t := by rw [htdef]; exact Real.sqrt_nonneg _
  obtain ⟨m, hmdef⟩ : ∃ m, m = ⌈t⌉₊ := ⟨_, rfl⟩
  have hm1 : t ≤ m := by rw [hmdef]; exact Nat.le_ceil t
  have hm2 : (m : ℝ) < t + 1 := by rw [hmdef]; exact Nat.ceil_lt_add_one ht0
  have hm16 : 16 ≤ m := by
    have : (16 : ℝ) < m := lt_of_lt_of_le ht hm1
    exact_mod_cast this.le
  have hlogn : Real.log n = t ^ 2 := by
    rw [htdef]; exact (Real.sq_sqrt (Real.log_nonneg hn1)).symm
  have hK0 : 0 ≤ K := by linarith
  have hK32 : K ^ 32 < 2 ^ m := by
    have h1 : K ^ 32 < Real.exp (Real.log 2 / 32 * t) ^ 32 :=
      pow_lt_pow_left₀ hcon hK0 (by norm_num)
    have h2 : Real.exp (Real.log 2 / 32 * t) ^ 32 ≤ 2 ^ m := by
      rw [← Real.exp_nat_mul]
      calc Real.exp (((32 : ℕ) : ℝ) * (Real.log 2 / 32 * t)) ≤
            Real.exp ((m : ℝ) * Real.log 2) := by
            apply Real.exp_le_exp.mpr
            have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
            push_cast
            nlinarith
        _ = 2 ^ m := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    exact h1.trans_le h2
  have hn3 : (n : ℝ) ≤ 3 ^ (m ^ 2) := by
    have h1 : Real.log n ≤ ((m ^ 2 : ℕ) : ℝ) := by
      rw [hlogn, Nat.cast_pow]
      exact pow_le_pow_left₀ ht0 hm1 2
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
      _ ≤ Real.exp ((m ^ 2 : ℕ) : ℝ) := Real.exp_le_exp.mpr h1
      _ = Real.exp 1 ^ (m ^ 2) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 3 ^ (m ^ 2) := by
          gcongr
          exact (Real.exp_one_lt_d9.trans (by norm_num)).le
  have hbad : 16 * K ^ 2 * ((m ^ 2 : ℕ) : ℝ) < 2 ^ m := by
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ((2 ^ 64 * m ^ 32 : ℕ) : ℝ) := ⟨_, rfl⟩
    have hm0 : 0 < m := by omega
    have hCpos : 0 < C := by
      rw [hCdef]
      exact_mod_cast (by positivity : 0 < 2 ^ 64 * m ^ 32)
    have hCle : C ≤ 2 ^ (15 * m) := by
      rw [hCdef]
      exact_mod_cast num_ineq m hm16
    have heq : (16 * K ^ 2 * ((m ^ 2 : ℕ) : ℝ)) ^ 16 = C * K ^ 32 := by
      rw [hCdef]; push_cast; ring
    have h16 : (16 * K ^ 2 * ((m ^ 2 : ℕ) : ℝ)) ^ 16 < (2 ^ m) ^ 16 := by
      rw [heq]
      calc C * K ^ 32 < C * 2 ^ m := mul_lt_mul_of_pos_left hK32 hCpos
        _ ≤ 2 ^ (15 * m) * 2 ^ m := mul_le_mul_of_nonneg_right hCle (by positivity)
        _ = (2 ^ m) ^ 16 := by rw [← pow_add, ← pow_mul]; ring_nf
    exact (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h16
  have hcore := hP (m ^ 2) m (by nlinarith) (by omega) hn3 hbad
  have hlow : (2 : ℝ) ^ ((m - 1) ^ 2) < n := by
    have h1 : ((m - 1 : ℕ) : ℝ) < t := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      linarith
    have h2 : (((m - 1) ^ 2 : ℕ) : ℝ) < Real.log n := by
      rw [hlogn, Nat.cast_pow]
      exact pow_lt_pow_left₀ h1 (Nat.cast_nonneg _) (by norm_num)
    calc (2 : ℝ) ^ ((m - 1) ^ 2) ≤ Real.exp 1 ^ ((m - 1) ^ 2) := by
          gcongr
          linarith [Real.add_one_le_exp 1]
      _ = Real.exp (((m - 1) ^ 2 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ < Real.exp (Real.log n) := Real.exp_lt_exp.mpr h2
      _ = n := Real.exp_log hnpos
  have hup : (n : ℝ) ^ 4 < 2 ^ ((32 + m) * m) := by
    have h1 : (n : ℝ) ^ 4 < ((162 * K ^ 8) ^ m) ^ 4 :=
      pow_lt_pow_left₀ hcore hnpos.le (by norm_num)
    have h2 : ((162 * K ^ 8) ^ m) ^ 4 = ((162 * K ^ 8) ^ 4) ^ m := by
      rw [← pow_mul, ← pow_mul, mul_comm m 4]
    obtain ⟨C1, hC1⟩ : ∃ C : ℝ, C = ((162 ^ 4 : ℕ) : ℝ) := ⟨_, rfl⟩
    obtain ⟨C2, hC2⟩ : ∃ C : ℝ, C = ((2 ^ 32 : ℕ) : ℝ) := ⟨_, rfl⟩
    have hC12 : C1 ≤ C2 := by
      rw [hC1, hC2]
      exact_mod_cast (by norm_num : 162 ^ 4 ≤ 2 ^ 32)
    have hC2pos : 0 ≤ C2 := by rw [hC2]; positivity
    have h3 : (162 * K ^ 8) ^ 4 ≤ (2 : ℝ) ^ (32 + m) := by
      calc (162 * K ^ 8) ^ 4 = C1 * K ^ 32 := by rw [hC1]; push_cast; ring
        _ ≤ C2 * 2 ^ m := mul_le_mul hC12 hK32.le (by positivity) hC2pos
        _ = 2 ^ (32 + m) := by rw [hC2, pow_add]; push_cast; ring
    calc (n : ℝ) ^ 4 < ((162 * K ^ 8) ^ 4) ^ m := h2 ▸ h1
      _ ≤ (2 ^ (32 + m)) ^ m := by gcongr
      _ = 2 ^ ((32 + m) * m) := by rw [← pow_mul]
  have hlow4 : (2 : ℝ) ^ ((32 + m) * m) ≤ (n : ℝ) ^ 4 := by
    calc (2 : ℝ) ^ ((32 + m) * m) ≤ 2 ^ (4 * (m - 1) ^ 2) :=
          pow_le_pow_right₀ (by norm_num) (exp_ineq m hm16)
      _ = (2 ^ ((m - 1) ^ 2)) ^ 4 := by rw [← pow_mul, mul_comm]
      _ ≤ (n : ℝ) ^ 4 := by gcongr
  linarith

/-- Compressing in every coordinate turns `B` into a down-set with as many points and with
`|A + Φ A| ≤ |B + Φ B|`. -/
private lemma exists_down {B : Finset (ℕ → ℤ)} {D0 : ℕ} (hB : Supp D0 B) :
    ∃ A : Finset (ℕ → ℤ), IsDown A ∧ Supp D0 A ∧ #A = #B ∧
      #(A + A.image shHom) ≤ #(B + B.image shHom) := by
  refine ⟨sweep 0 D0 B, ?_, supp_sweep 0 D0 B hB (by omega), card_sweep 0 D0 B, ?_⟩
  · exact isDown_of_isComp (fun i hi => isComp_sweep 0 D0 B i (Nat.zero_le _) (by omega))
      (supp_sweep 0 D0 B hB (by omega))
  · have h1 := card_sweep_add_sweep_le 0 (D0 + 1) B (B.image shHom)
    have h2 : sweep 0 (D0 + 1) (B.image shHom) = (sweep 0 D0 B).image shHom := by
      rw [show sweep 0 (D0 + 1) (B.image shHom) = comp 0 (sweep 1 D0 (B.image shHom)) from rfl,
        sweep_sh, comp_eq_self]
      intro x hx
      obtain ⟨y, _, rfl⟩ := mem_image.mp hx
      exact shHom_zero y
    have h3 : sweep 0 (D0 + 1) B = sweep 0 D0 B := by
      rw [sweep_succ', zero_add, comp_eq_self (fun x hx => hB x hx D0 le_rfl)]
    rw [h2, h3] at h1
    exact h1

/-- The theorem of Conlon and Lim for coefficient vectors, when `√(log |B|) > 16`. -/
private lemma main_comb {B : Finset (ℕ → ℤ)} {D0 : ℕ} (hB : Supp D0 B) (hne : B.Nonempty)
    (ht : 16 < Real.sqrt (Real.log #B)) :
    Real.exp (Real.log 2 / 32 * Real.sqrt (Real.log #B)) * #B ≤ #(B + B.image shHom) := by
  obtain ⟨A, hAdown, hAsupp, hAcard, hAsum⟩ := exists_down hB
  have hAne : A.Nonempty := card_pos.mp (hAcard ▸ hne.card_pos)
  rw [← hAcard] at ht ⊢
  have hnpos : (0 : ℝ) < #A := by exact_mod_cast hAne.card_pos
  have hK1 : 1 ≤ (#(A + A.image shHom) : ℝ) / #A := by
    rw [le_div_iff₀ hnpos, one_mul]
    exact_mod_cast card_le_card_add_sh hAne
  have hfin := final_num #A ((#(A + A.image shHom) : ℝ) / #A) hAne.card_pos hK1
    (fun h L hh hL hn3 hbad => core hAdown hAne hAsupp h L hh hL hn3 hbad) ht
  calc Real.exp (Real.log 2 / 32 * Real.sqrt (Real.log #A)) * #A ≤
        ((#(A + A.image shHom) : ℝ) / #A) * #A := by gcongr
    _ = #(A + A.image shHom) := by field_simp
    _ ≤ #(B + B.image shHom) := by exact_mod_cast hAsum

end Proof

open Finset

/-- **Conlon–Lim theorem on sums of transcendental dilates.** There is a real constant $c > 0$
such that for every real number $\alpha$ transcendental over $\mathbb{Q}$ and every finite set $A$
of real numbers,
$$e^{c\sqrt{\log |A|}}\,|A| \le |A + \alpha \cdot A|,$$
where $A + \alpha \cdot A = \{a + \alpha b : a, b \in A\}$.

Resolved true: Conlon and Lim prove that there is an absolute constant `c > 0` such that `|A + λ·A|
≥ e^{c √(log |A|)} |A|` for every finite `A ⊆ ℝ` and every transcendental `λ ∈ ℝ`, best possible up
to the constant `c` by the construction of Konyagin and Łaba.

Source: Problems presented at the
workshop on recent trends in additive combinatorics, collected by E. Croot and V. F. Lev, AIM
workshop problem list, Problem 4.8 (I. Łaba), https://aimath.org/WWN/additivecomb/additivecomb.pdf;
resolution: D. Conlon and J. Lim, Sums of transcendental dilates, Bull. London Math. Soc. 55 (2023)
2400-2406, arXiv:2212.10128, abstract and main theorem, https://arxiv.org/abs/2212.10128.
-/
public theorem transcendentalDilateLowerBound_holds : transcendentalDilateLowerBound := by
  refine ⟨Real.log 2 / 32, by positivity, fun α hα A => ?_⟩
  rcases Nat.lt_or_ge #A 2 with hA | hA
  · rcases Nat.lt_succ_iff.mp hA |>.lt_or_eq with hA0 | hA1
    · have : #A = 0 := by omega
      rw [this]
      simp
    · have hne : A.Nonempty := card_pos.mp (by omega)
      rw [hA1]
      simp only [Nat.cast_one, Real.log_one, Real.sqrt_zero, mul_zero, Real.exp_zero, one_mul]
      have h1 : 1 ≤ #(A + α • A) :=
        Nat.one_le_iff_ne_zero.mpr (hne.add hne.smul_finset).card_pos.ne'
      exact_mod_cast h1
  have hne : A.Nonempty := card_pos.mp (by omega)
  by_cases ht : Real.sqrt (Real.log #A) ≤ 16
  · have hα0 : α ≠ 0 := fun h => hα (h ▸ isAlgebraic_zero)
    have hcard : #(α • A) = #A := by
      rw [smul_finset_def, card_image_of_injective]
      intro x y hxy
      exact mul_left_cancel₀ hα0 hxy
    have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hne hne.smul_finset (t := α • A)
    rw [hcard] at hcd
    have hexp : Real.exp (Real.log 2 / 32 * Real.sqrt (Real.log #A)) ≤ 3 / 2 := by
      have h1 : Real.exp (Real.log 2 / 32 * Real.sqrt (Real.log #A)) ≤
          Real.exp (Real.log 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        nlinarith
      have h2 : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
        rw [← Real.exp_nat_mul]
        push_cast
        rw [show (2 : ℝ) * (Real.log 2 / 2) = Real.log 2 by ring, Real.exp_log (by norm_num)]
      have h3 : Real.exp (Real.log 2 / 2) ≤ 3 / 2 := by
        nlinarith [Real.exp_pos (Real.log 2 / 2)]
      linarith
    have hn2 : (2 : ℝ) ≤ #A := by exact_mod_cast hA
    have hcd' : (2 * #A - 1 : ℝ) ≤ #(A + α • A) := by
      have : #A + #A - 1 ≤ #(A + α • A) := hcd
      have h2 : ((#A + #A - 1 : ℕ) : ℝ) = 2 * #A - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← h2]
      exact_mod_cast this
    calc Real.exp (Real.log 2 / 32 * Real.sqrt (Real.log #A)) * #A ≤ 3 / 2 * #A := by gcongr
      _ ≤ 2 * #A - 1 := by linarith
      _ ≤ #(A + α • A) := hcd'
  · push Not at ht
    obtain ⟨B, D0, hBcard, hBsupp, hBsum⟩ := kp_reduction α hα A
    have hBne : B.Nonempty := card_pos.mp (hBcard ▸ hne.card_pos)
    rw [← hBcard] at ht ⊢
    exact (main_comb hBsupp hBne ht).trans (by exact_mod_cast hBsum)

end MathlibExt.Combinatorics.TranscendentalDilateSumsetAIMCombinatoricsProblem264Wanted
