/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCatalog
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence

/-! A finite source-faithful parameter space for norm-eight lattice vectors.
The common parity and Golay word are uniquely recovered from coordinate residues;
coordinates are bounded by the norm, rather than by an assumed catalogue count. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The actual integral norm-eight vectors. -/
def LeechNormEight := {u : leechIntegral // leechSquareSum u.val = 64}

/-- Enumerate exactly the integer interval from minus eight to eight. -/
def leechNormEightCoordinate (a : Fin 17) : ℤ := (a.val : ℤ) - 8

theorem leechNormEightCoordinate_injective : Function.Injective leechNormEightCoordinate := by
  intro a b h
  apply Fin.ext
  unfold leechNormEightCoordinate at h
  omega

/-- Source solutions with all coordinates bounded by their actual norm. -/
def LeechNormEightBoundedSolution (m : Bool) (c : golayCode) :=
  {a : Fin 24 → Fin 17 //
    (∀ i, (leechNormEightCoordinate (a i) : ZMod 4) =
      (m.toNat : ZMod 4) + 2 * ((c.val i).val : ZMod 4)) ∧
    (∑ i, (leechNormEightCoordinate (a i)).natAbs ^ 2) = 64 ∧
    ((∑ i, leechNormEightCoordinate (a i) : ℤ) : ZMod 8) = 4 * (m.toNat : ZMod 8)}

instance (m : Bool) (c : golayCode) : Fintype (LeechNormEightBoundedSolution m c) :=
  by
    unfold LeechNormEightBoundedSolution
    infer_instance

/-- Both allowed source parities and all actual Golay words, with their solutions. -/
def LeechNormEightSource := Σ m : Bool, Σ c : golayCode, LeechNormEightBoundedSolution m c

noncomputable instance : Fintype LeechNormEightSource := by
  unfold LeechNormEightSource
  letI := Fintype.ofFinite golayCode
  infer_instance

/-- Forget the uniquely determined source residues. -/
def leechNormEightSourceVector (s : LeechNormEightSource) : LeechNormEight := by
  refine ⟨⟨fun i => leechNormEightCoordinate (s.2.2.val i), ?_⟩, ?_⟩
  · apply (mem_leechIntegral_iff_source _).mpr
    refine ⟨(s.1.toNat : ℤ), ?_, s.2.1.val, s.2.1.property, ?_, ?_⟩
    · cases s.1 <;> simp
    · simpa only [Int.cast_natCast] using s.2.2.property.1
    · simpa only [Int.cast_natCast] using s.2.2.property.2.2
  · have h : ((∑ i, (leechNormEightCoordinate (s.2.2.val i)).natAbs ^ 2 : ℕ) : ℤ) =
        leechSquareSum (fun i => leechNormEightCoordinate (s.2.2.val i)) := by
      simp only [Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, leechSquareSum, sq_abs]
    rw [s.2.2.property.2.1] at h
    exact h.symm

private theorem leechNormEight_residue_unique (m n : Bool) (b d : ZMod 2)
    (h : (m.toNat : ZMod 4) + 2 * (b.val : ZMod 4) =
      (n.toNat : ZMod 4) + 2 * (d.val : ZMod 4)) : m = n ∧ b = d := by
  have hc : ∀ m n : Bool, ∀ b d : ZMod 2,
      (m.toNat : ZMod 4) + 2 * (b.val : ZMod 4) =
      (n.toNat : ZMod 4) + 2 * (d.val : ZMod 4) → m = n ∧ b = d := by decide
  exact hc m n b d h

/-- The source parity and binary word introduce no multiplicities in the count. -/
theorem leechNormEightSourceVector_injective : Function.Injective leechNormEightSourceVector := by
  rintro ⟨m, c, a, ha⟩ ⟨n, d, b, hb⟩ h
  have hv : (fun i => leechNormEightCoordinate (a i)) =
      (fun i => leechNormEightCoordinate (b i)) := by
    simpa only [leechNormEightSourceVector] using congrArg (fun u => u.val.val) h
  have hr (i : Fin 24) := leechNormEight_residue_unique m n (c.val i) (d.val i)
    ((ha.1 i).symm.trans ((congrArg (fun u => (u i : ZMod 4)) hv).trans (hb.1 i)))
  have hmn := (hr 0).1
  subst n
  have hcd : c = d := Subtype.ext (funext fun i => (hr i).2)
  subst d
  have hab : a = b := funext fun i => leechNormEightCoordinate_injective (congrFun hv i)
  subst b
  rfl

/-- Every actual norm-eight lattice vector occurs in the finite source space. -/
theorem leechNormEightSourceVector_surjective : Function.Surjective leechNormEightSourceVector := by
  rintro ⟨u, hn⟩
  obtain ⟨m, hm, c, hc, hr, hh⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  have hb (i : Fin 24) := leechNormEight_natAbs_le u.val hn i
  let a : Fin 24 → Fin 17 := fun i => ⟨(u.val i + 8).toNat, by
    have h : |u.val i| ≤ (8 : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hb i
    obtain ⟨hl, hh⟩ := abs_le.mp h
    omega⟩
  have ha (i : Fin 24) : leechNormEightCoordinate (a i) = u.val i := by
    have h : |u.val i| ≤ (8 : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hb i
    obtain ⟨hl, hh⟩ := abs_le.mp h
    dsimp [a, leechNormEightCoordinate]
    omega
  have han : (∑ i, (leechNormEightCoordinate (a i)).natAbs ^ 2) = 64 := by
    simpa only [ha] using leechNormEight_natSquareSum u.val hn
  rcases hm with rfl | rfl
  · refine ⟨⟨false, ⟨c, hc⟩, a, ?_⟩, ?_⟩
    · exact ⟨by simpa [ha] using hr, han, by simpa [ha] using hh⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact funext ha
  · refine ⟨⟨true, ⟨c, hc⟩, a, ?_⟩, ?_⟩
    · exact ⟨by simpa [ha] using hr, han, by simpa [ha] using hh⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact funext ha

/-- Genuine finite enumeration of actual norm-eight vectors. -/
noncomputable def leechNormEightSourceEquiv : LeechNormEightSource ≃ LeechNormEight :=
  Equiv.ofBijective leechNormEightSourceVector
    ⟨leechNormEightSourceVector_injective, leechNormEightSourceVector_surjective⟩

instance : Finite LeechNormEight := Finite.of_equiv _ leechNormEightSourceEquiv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
