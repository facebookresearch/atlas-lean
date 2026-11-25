/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ReflectionCalculus

/-!
# Kripke completeness of the Reflection Calculus

A sequent of RC is derivable exactly when it is valid on every RC-frame
(`Cslib.Modal.RC.derives_iff_forall_frame`). We construct the canonical model on deductively
closed theories for modalities in `ℕ`, following Section 4 of Beklemishev, "Positive provability
logic for uniform reflection principles", arXiv:1304.4396v3.
-/

namespace Cslib.Modal.RC

universe u

variable {Atom : Type u}

-- A world contains truth and is closed under conjunction and derivable consequences.
private structure Theory (Atom : Type u) where
  holds : Formula Atom → Prop
  top : holds .top
  conj : ∀ {A B}, holds A → holds B → holds (.and A B)
  cut : ∀ {A B}, Derives A B → holds A → holds B

private def principal (A : Formula Atom) : Theory Atom where
  holds := Derives A
  top := .top A
  conj := .and_intro
  cut h hA := hA.trans h

-- At an n-successor every formula gives an n-diamond at the predecessor, and all
-- lower diamonds of the predecessor persist at the successor.
private structure Access (n : ℕ) (x y : Theory Atom) : Prop where
  lift : ∀ {A}, y.holds A → x.holds (.dia n A)
  persist : ∀ {k A}, k < n → x.holds (.dia k A) → y.holds (.dia k A)

private theorem canonicalFrame : IsFrame (Access (Atom := Atom)) where
  polytrans {m n x y z} hxy hyz := by
    constructor
    · intro A hA
      have h := hxy.lift (hyz.lift hA)
      rcases Nat.le_total m n with hmn | hnm
      · simpa [Nat.min_eq_left hmn] using x.cut (.dia_dia_of_le' hmn A) h
      · simpa [Nat.min_eq_right hnm] using x.cut (.dia_dia_of_le hnm A) h
    · intro k A h hx
      exact hyz.persist (Nat.lt_of_lt_of_le h (Nat.min_le_right ..))
        (hxy.persist (Nat.lt_of_lt_of_le h (Nat.min_le_left ..)) hx)
  condJ {m n x y z} hnm hxy hxz := by
    constructor
    · exact fun hz ↦ hxy.persist hnm (hxz.lift hz)
    · intro k A hkn hy
      have hkm := Nat.le_of_lt (Nat.lt_trans hkn hnm)
      exact hxz.persist hkn (x.cut (.dia_dia_of_le hkm A) (hxy.lift hy))
  monotone {m n x y} hnm hxy :=
    ⟨fun hy ↦ x.cut (.monotone hnm _) (hxy.lift hy),
      fun hkn ↦ hxy.persist (Nat.lt_trans hkn hnm)⟩

-- To witness ⟨n⟩B at x, take the formulas C that can be conjoined to every refinement
-- D ⊢ B for which x contains ⟨n⟩D. Two such formulas can be conjoined successively,
-- since D ∧ C still refines B. The RC interaction axiom supplies every lower diamond.
private def successor (x : Theory Atom) (n : ℕ) (B : Formula Atom) : Theory Atom where
  holds C := ∀ D, Derives D B → x.holds (.dia n D) → x.holds (.dia n (.and D C))
  top D _ hD := x.cut (.dia_mono n (.and_intro (.refl D) (.top D))) hD
  conj {C E} hC hE D hDB hD := by
    have h := hE (.and D C) ((Derives.and_left D C).trans hDB) (hC D hDB hD)
    have hDC := Derives.and_left (.and D C) E
    have reassoc := (hDC.trans (.and_left D C)).and_intro
      ((hDC.trans (.and_right D C)).and_intro (.and_right _ E))
    exact x.cut (.dia_mono n reassoc) h
  cut h hC D hDB hD :=
    x.cut (.dia_mono n (.and_intro (.and_left _ _) ((Derives.and_right _ _).trans h)))
      (hC D hDB hD)

private theorem exists_successor {x : Theory Atom} {n : ℕ} {B : Formula Atom}
    (hB : x.holds (.dia n B)) : ∃ y, Access n x y ∧ y.holds B := by
  refine ⟨successor x n B, ⟨?_, ?_⟩, ?_⟩
  · intro C hC
    exact x.cut (.dia_mono n (.and_right B C)) (hC B (.refl B) hB)
  · intro k C hkn hk D _ hD
    exact x.cut (.dia_and hkn D C) (x.conj hD hk)
  · intro D hDB hD
    exact x.cut (.dia_mono n (.and_intro (.refl D) hDB)) hD

private theorem canonical_truth (A : Formula Atom) (x : Theory Atom) :
    Satisfies Access (fun y p ↦ y.holds (.atom p)) x A ↔ x.holds A := by
  induction A generalizing x with
  | atom => rfl
  | top => exact ⟨fun _ ↦ x.top, fun _ ↦ trivial⟩
  | and A B ihA ihB =>
    exact ⟨fun ⟨ha, hb⟩ ↦ x.conj ((ihA x).mp ha) ((ihB x).mp hb),
      fun h ↦ ⟨(ihA x).mpr (x.cut (.and_left A B) h), (ihB x).mpr (x.cut (.and_right A B) h)⟩⟩
  | dia n B ih =>
    constructor
    · rintro ⟨y, hxy, hy⟩
      exact hxy.lift ((ih y).mp hy)
    · intro h
      obtain ⟨y, hxy, hy⟩ := exists_successor h
      exact ⟨y, hxy, (ih y).mpr hy⟩

/-- **Kripke completeness of RC.** A sequent `A ⊢ B` of strictly positive formulas is derivable in
RC iff every world satisfying `A` satisfies `B` in every Kripke model on an RC-frame. The source
proves this for the language with modalities in `ω + 1` (Beklemishev, "Positive provability logic
for uniform reflection principles", arXiv:1304.4396v3, Theorem 1(ii)); the restriction to
modalities in `ℕ` stated here follows from it with the conservativity of RC over its fragments
(Theorem 2 there), since an RC-model restricts to a model on an RC-frame for `ℕ`. The direction
from left to right is the proved `Derives.sound`. -/
public theorem derives_iff_forall_frame {Atom : Type u} (A B : Formula Atom) :
    Derives A B ↔
      ∀ (W : Type u) (R : ℕ → W → W → Prop) (V : W → Atom → Prop), IsFrame R →
        ∀ x, Satisfies R V x A → Satisfies R V x B := by
  constructor
  · exact fun h _ _ V hR ↦ h.sound hR V
  · intro valid
    let x := principal A
    have hA := (canonical_truth A x).mpr (.refl A)
    exact (canonical_truth B x).mp (valid _ _ _ canonicalFrame x hA)

end Cslib.Modal.RC
