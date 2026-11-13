/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.RSW.Defs

open Set

namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice
open StatMech.TwoDim










def annulusEvent (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  annulusCircuitEvent (fun _ => 0) n

@[simp] theorem mem_annulusEvent {n : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ annulusEvent n ↔ AnnulusCircuit ω (fun _ => 0) n := Iff.rfl







def rp5_P5a (μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ μ n (annulusEvent n)







def rp5_P5b (ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ ν R n (annulusEvent n)


















theorem rp5_p5a_p5b
    {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    (hcmp : ∀ R n : ℕ, μ n (annulusEvent n) ≤ ν R n (annulusEvent n))
    (h : rp5_P5a μ) : rp5_P5b ν := by
  obtain ⟨c, hc, hμ⟩ := h
  intro R _hR
  refine ⟨c, hc, fun n => ?_⟩
  exact (hμ n).trans (hcmp R n)













theorem rp5_p5_p5a
    {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    (hglue : ∀ n : ℕ,
      (μ n (boxCrossingEvent 10 n)) ^ 4 ≤ μ n (annulusEvent n))
    (h : P5 μ) : rp5_P5a μ := by
  obtain ⟨c, hc, hμ⟩ := h 10 (by norm_num)
  refine ⟨c ^ 4, by positivity, fun n => ?_⟩
  
  refine le_trans ?_ (hglue n)
  have hcle : c ≤ μ n (boxCrossingEvent 10 n) := hμ n
  exact pow_le_pow_left₀ hc.le hcle 4












theorem rp5_p5b_p5_lower
    {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    {lam : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    (hchain : ∀ (α : ℝ) (n : ℕ),
      ν 2 n (annulusEvent n) ≤ lam n (boxCrossingEvent α n))
    (h : rp5_P5b ν) : P5 lam := by
  obtain ⟨c, hc, hν⟩ := h 2 le_rfl
  intro α _hα
  refine ⟨c, hc, fun n => ?_⟩
  exact (hν n).trans (hchain α n)












theorem rp5_p5b_p5_upper
    {μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    {compl : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    {α : ℝ} {c : ℝ} (_hc : 0 < c)
    (hnorm : ∀ n : ℕ,
      μ n (boxCrossingEvent α n) + compl n (boxCrossingEvent α n) = 1)
    (hdual : ∀ n : ℕ, c ≤ compl n (boxCrossingEvent α n)) :
    ∀ n : ℕ, μ n (boxCrossingEvent α n) ≤ 1 - c := by
  intro n
  have h := hnorm n
  have hd := hdual n
  linarith















theorem rp5_p5_p5c
    {Ξ : Type*} {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    (hlower : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ (ξ : Ξ) (n : ℕ),
      c ≤ μ ξ n (boxCrossingEvent α n) ∧ μ ξ n (boxCrossingEvent α n) ≤ 1 - c) :
    P5c μ := hlower































theorem rp5_p5_equiv
    {Ξ : Type*} (ξ₀ : Ξ)
    {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    {ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    
    (hcmp : ∀ R n : ℕ, μ ξ₀ n (annulusEvent n) ≤ ν R n (annulusEvent n))
    
    (hglue : ∀ n : ℕ,
      (μ ξ₀ n (boxCrossingEvent 10 n)) ^ 4 ≤ μ ξ₀ n (annulusEvent n))
    
    (hchain : ∀ (α : ℝ) (n : ℕ),
      ν 2 n (annulusEvent n) ≤ μ ξ₀ n (boxCrossingEvent α n))
    
    (htwo : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ (ξ : Ξ) (n : ℕ),
      c ≤ μ ξ n (boxCrossingEvent α n) ∧ μ ξ n (boxCrossingEvent α n) ≤ 1 - c) :
    
    (P5 (μ ξ₀) ↔ rp5_P5a (μ ξ₀)) ∧
    (rp5_P5a (μ ξ₀) → rp5_P5b ν) ∧
    (rp5_P5b ν → P5 (μ ξ₀)) ∧
    (P5 (μ ξ₀) ↔ P5c μ) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩
  · 
    intro h; exact rp5_p5_p5a hglue h
  · 
    intro h
    have hb : rp5_P5b ν := rp5_p5a_p5b hcmp h
    exact rp5_p5b_p5_lower hchain hb
  · 
    intro h; exact rp5_p5a_p5b hcmp h
  · 
    intro h; exact rp5_p5b_p5_lower hchain h
  · 
    intro _; exact rp5_p5_p5c htwo
  · 
    intro h; exact h.p5 ξ₀

end Box

end RSW

end StatMech
