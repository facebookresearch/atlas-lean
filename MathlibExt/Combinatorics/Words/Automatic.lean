/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Words.CobhamUniformMorphism
import Mathlib.Tactic

set_option autoImplicit false

namespace MetaMathlibExt

@[expose] public section

/-!
# Automatic sequences: finite kernels and the Eilenberg bridge

Generic automatic-sequence infrastructure (no power-series data): the
`k`-kernel of a sequence, `k`-automaticity via finiteness of the kernel,
kernel finiteness lemmas, and Eilenberg's equivalence with the DFAO
notion `IsKAutomaticSequence` from
`MathlibExt.Combinatorics.Words.CobhamUniformMorphism`. Moved here from
`MathlibExt.RingTheory.PowerSeries.Christol`, which imports this
module, so automata users do not need the Christol/algebra dependency
closure.
-/

/-- One-dimensional `k`-kernel of a sequence.

Source: Adamczewski--Bell, arXiv:1205.4091v1, lines 1105--1129.
The finite-kernel representation: the kernel is the set of all subsequence
maps `n ↦ a (k ^ e * n + r)` as `e : ℕ` varies over exponents and
`r : ℕ` varies over residues with `r < k ^ e`. Each member is hence
recorded as an explicit pair `(e, r)` together with the equality to the
corresponding decimated subsequence. -/
public def kKernel (k : ℕ) {Δ : Type*} (a : ℕ → Δ) : Set (ℕ → Δ) :=
  {b | ∃ e : ℕ, ∃ r : ℕ, r < k ^ e ∧ b = fun n => a (k ^ e * n + r)}

/-- `k`-automaticity of a sequence via the Eilenberg finite-kernel characterization.

Sources: Adamczewski--Bell, arXiv:1205.4091v1, lines 160--195 for the
finite-automaton (DFAO) definition, and lines 1105--1129 for Eilenberg's
equivalence between `k`-automaticity and finiteness of the `k`-kernel.
A sequence is `k`-automatic when `2 ≤ k` and its `k`-kernel `kKernel k a`
is finite. -/
public def IsKAutomatic (k : ℕ) {Δ : Type*} (a : ℕ → Δ) : Prop :=
  2 ≤ k ∧ Finite ↥(kKernel k a)

section ChrKernel

variable {Δ : Type*}

/-- The `(p ^ r)`-kernel is contained in the `p`-kernel. -/
theorem chr_qkernel_subset {p r : ℕ} (a : ℕ → Δ) :
    kKernel (p ^ r) a ⊆ kKernel p a := by
  intro b hb
  obtain ⟨e, R, hR, rfl⟩ := hb
  refine ⟨r * e, R, by rwa [pow_mul], funext fun n => ?_⟩
  rw [← pow_mul]

/-- Embedding of `(kernel) × (residue data)` into sequences, used to bound
the `p`-kernel by the `(p ^ r)`-kernel. -/
private def chr_emb (p r : ℕ) (a : ℕ → Δ)
    (x : ↥(kKernel (p ^ r) a) × (Σ _s : Fin r, Fin (p ^ _s.val))) (n : ℕ) : Δ :=
  (x.1 : ℕ → Δ) (p ^ (x.2.1.val) * n + x.2.2.val)

/-- If the `(p ^ r)`-kernel is finite then so is the `p`-kernel. -/
theorem chr_pkernel_finite {p r : ℕ} (hr : 0 < r) (hp : 0 < p)
    (a : ℕ → Δ) [Finite ↥(kKernel (p ^ r) a)] :
    Finite ↥(kKernel p a) := by
  have hfinR : (Set.range (chr_emb p r a)).Finite := Set.finite_range _
  rw [Set.finite_coe_iff]
  apply hfinR.subset
  intro b hb
  obtain ⟨e, R, hR, rfl⟩ := hb
  have hDpos : 0 < (p ^ r) ^ (e / r) := pow_pos (pow_pos hp r) _
  have he : p ^ e = (p ^ r) ^ (e / r) * p ^ (e % r) := by
    conv_lhs => rw [← Nat.div_add_mod e r, pow_add]
    rw [pow_mul]
  have hRs : R / (p ^ r) ^ (e / r) < p ^ (e % r) := by
    rw [Nat.div_lt_iff_lt_mul hDpos, mul_comm]
    omega
  have hcmem : (fun m => a ((p ^ r) ^ (e / r) * m + R % (p ^ r) ^ (e / r)))
      ∈ kKernel (p ^ r) a :=
    ⟨e / r, R % (p ^ r) ^ (e / r), Nat.mod_lt _ hDpos, rfl⟩
  refine ⟨⟨⟨_, hcmem⟩, ⟨⟨e % r, Nat.mod_lt _ hr⟩,
    ⟨R / (p ^ r) ^ (e / r), hRs⟩⟩⟩, funext fun n => ?_⟩
  have heq : p ^ e * n + R = (p ^ r) ^ (e / r)
        * (p ^ (e % r) * n + R / (p ^ r) ^ (e / r))
        + R % (p ^ r) ^ (e / r) := by
    conv_lhs => rw [he, ← Nat.div_add_mod R ((p ^ r) ^ (e / r))]
    ring
  rw [heq]
  rfl

/-- The `q`-kernel is stable under `n ↦ b (q * n + j)` for `j < q`. -/
theorem chr_kernel_lam_mem {q : ℕ} {a b : ℕ → Δ}
    (hb : b ∈ kKernel q a) {j : ℕ} (hj : j < q) :
    (fun n => b (q * n + j)) ∈ kKernel q a := by
  obtain ⟨e, R, hR, rfl⟩ := hb
  refine ⟨e + 1, q ^ e * j + R, ?_, funext fun n => ?_⟩
  · rw [pow_succ]
    have h1 : q ^ e * j + R < q ^ e * j + q ^ e :=
      Nat.add_lt_add_left hR _
    have h2 : q ^ e * (j + 1) = q ^ e * j + q ^ e := by ring
    have h3 : q ^ e * (j + 1) ≤ q ^ e * q := Nat.mul_le_mul_left _ hj
    omega
  · simp only []
    congr 1
    rw [pow_succ]
    ring

/-- Every sequence is in its own `q`-kernel. -/
theorem chr_self_mem_kernel {q : ℕ} (a : ℕ → Δ) :
    a ∈ kKernel q a := by
  refine ⟨0, 0, by simp, ?_⟩
  funext n
  simp

end ChrKernel

section ChrAuto

variable {B : Type*}

/-- Bridge: `baseWordValueLSD` equals `Nat.ofDigits` on mapped digits. -/
private theorem chr_base_eq_ofDigits {k : ℕ} (ds : List (Fin k)) :
    baseWordValueLSD ds = Nat.ofDigits k (ds.map Fin.val) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    change d.val + k * baseWordValueLSD ds = _
    rw [List.map_cons, Nat.ofDigits_cons, ih]

/-- Value of a concatenation: low part plus shifted high part. -/
private theorem chr_base_append {k : ℕ} (xs ys : List (Fin k)) :
    baseWordValueLSD (xs ++ ys)
      = baseWordValueLSD xs + k ^ xs.length * baseWordValueLSD ys := by
  rw [chr_base_eq_ofDigits, chr_base_eq_ofDigits, chr_base_eq_ofDigits,
    List.map_append, Nat.ofDigits_append, List.length_map]

/-- Mapping a `pmap` digit word back through `Fin.val` recovers the digits. -/
private theorem chr_map_pmap_val {k : ℕ} (l : List ℕ)
    (f : ∀ d : ℕ, d < k → Fin k) (hf : ∀ d h, (f d h).val = d)
    (H : ∀ d ∈ l, d < k) :
    ((l.pmap f H).map Fin.val) = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [List.pmap_cons, List.map_cons, hf, ih]

/-- Every `n` has a representing word. -/
private theorem chr_exists_word {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    ∃ ds : List (Fin k), baseWordValueLSD ds = n := by
  have hk1 : 1 < k := by omega
  have hmem : ∀ d ∈ Nat.digits k n, d < k :=
    fun d hd => Nat.digits_lt_base hk1 hd
  refine ⟨(Nat.digits k n).pmap (fun d h => (⟨d, h⟩ : Fin k)) hmem, ?_⟩
  rw [chr_base_eq_ofDigits,
    chr_map_pmap_val _ _ (fun d h => rfl) hmem, Nat.ofDigits_digits]

/-- A zero word has value zero. -/
private theorem chr_base_replicate_zero {k : ℕ} (hk : 0 < k) (t : ℕ) :
    baseWordValueLSD (List.replicate t (⟨0, hk⟩ : Fin k)) = 0 := by
  rw [chr_base_eq_ofDigits, List.map_replicate]
  exact Nat.ofDigits_replicate_zero

/-- Every `r < k ^ e` has a representing word of length exactly `e`. -/
private theorem chr_exists_word_len {k : ℕ} (hk : 2 ≤ k) (e r : ℕ)
    (h : r < k ^ e) :
    ∃ ds : List (Fin k), ds.length = e ∧ baseWordValueLSD ds = r := by
  have hk1 : 1 < k := by omega
  have hk0 : 0 < k := by omega
  have hmem : ∀ d ∈ Nat.digits k r, d < k :=
    fun d hd => Nat.digits_lt_base hk1 hd
  set base := (Nat.digits k r).pmap (fun d h => (⟨d, h⟩ : Fin k)) hmem with hbasedef
  have hbase_len : base.length = (Nat.digits k r).length := List.length_pmap
  have hbase_val : baseWordValueLSD base = r := by
    rw [chr_base_eq_ofDigits,
      chr_map_pmap_val _ _ (fun d h => rfl) hmem, Nat.ofDigits_digits]
  have hlen : base.length ≤ e := by
    rw [hbase_len]
    exact (Nat.digits_length_le_iff hk1 r).mpr h
  refine ⟨base ++ List.replicate (e - base.length) (⟨0, hk0⟩ : Fin k), ?_, ?_⟩
  · rw [List.length_append, List.length_replicate,
      Nat.add_sub_cancel' hlen]
  · rw [chr_base_append, hbase_val, chr_base_replicate_zero hk0,
      mul_zero, add_zero]

/-- One-step decimation of a kernel element by a digit. -/
private def chr_step {k : ℕ} {a : ℕ → B} (b : ↥(kKernel k a)) (d : Fin k) :
    ↥(kKernel k a) :=
  ⟨fun n => b.val (k * n + d.val), chr_kernel_lam_mem b.prop d.isLt⟩

/-- Reading a word from a kernel element stays in the kernel. -/
private theorem chr_read_mem {k : ℕ} {a : ℕ → B}
    (ds : List (Fin k)) (b : ↥(kKernel k a)) :
    (fun n => b.val (k ^ ds.length * n + baseWordValueLSD ds)) ∈ kKernel k a := by
  induction ds generalizing b with
  | nil =>
    have h0 : baseWordValueLSD ([] : List (Fin k)) = 0 := rfl
    have hfun : (fun n => b.val
        (k ^ ([] : List (Fin k)).length * n
          + baseWordValueLSD ([] : List (Fin k)))) = b.val := by
      funext n
      simp [h0]
    rw [hfun]
    exact b.prop
  | cons d ds ih =>
    have hcons : baseWordValueLSD (d :: ds)
        = d.val + k * baseWordValueLSD ds := rfl
    have hfun : (fun n => b.val (k ^ (d :: ds).length * n + baseWordValueLSD (d :: ds)))
        = (fun n => (chr_step b d).val (k ^ ds.length * n + baseWordValueLSD ds)) := by
      funext n
      change b.val (k ^ (d :: ds).length * n + baseWordValueLSD (d :: ds))
        = b.val (k * (k ^ ds.length * n + baseWordValueLSD ds) + d.val)
      rw [show (d :: ds).length = ds.length + 1 from rfl, hcons, pow_succ,
        show k ^ ds.length * k * n + (d.val + k * baseWordValueLSD ds)
          = k * (k ^ ds.length * n + baseWordValueLSD ds) + d.val from by ring]
    rw [hfun]
    exact ih (chr_step b d)

/-- Folding a word from `e b` lands in the explicit decimated map. -/
private theorem chr_fold_val {k : ℕ} {a : ℕ → B}
    (q : ℕ) (e : ↥(kKernel k a) ≃ Fin q)
    (trans : Fin q → Fin k → Fin q)
    (htrans : ∀ (s : Fin q) (d : Fin k),
      trans s d = e (chr_step (e.symm s) d))
    (ds : List (Fin k)) (b : ↥(kKernel k a)) :
    ds.foldl trans (e b)
      = e ⟨fun n => b.val (k ^ ds.length * n + baseWordValueLSD ds),
        chr_read_mem ds b⟩ := by
  induction ds generalizing b with
  | nil =>
    have h0 : baseWordValueLSD ([] : List (Fin k)) = 0 := rfl
    have hfun : (fun n => b.val
        (k ^ ([] : List (Fin k)).length * n
          + baseWordValueLSD ([] : List (Fin k)))) = b.val := by
      funext n
      simp [h0]
    simp only [List.foldl_nil]
    exact congrArg e (Subtype.ext hfun).symm
  | cons d ds ih =>
    have hcons : baseWordValueLSD (d :: ds)
        = d.val + k * baseWordValueLSD ds := rfl
    rw [List.foldl_cons, htrans, Equiv.symm_apply_apply, ih]
    apply congrArg e
    apply Subtype.ext
    funext n
    change b.val (k * (k ^ ds.length * n + baseWordValueLSD ds) + d.val)
      = b.val (k ^ (d :: ds).length * n + baseWordValueLSD (d :: ds))
    rw [show (d :: ds).length = ds.length + 1 from rfl, hcons, pow_succ,
      show k * (k ^ ds.length * n + baseWordValueLSD ds) + d.val
        = k ^ ds.length * k * n + (d.val + k * baseWordValueLSD ds) from by ring]

/-- Eilenberg's equivalence: finite kernel iff DFAO-computable. -/
public theorem isKAutomatic_iff_isKAutomaticSequence {B : Type} [Fintype B]
    (k : ℕ) (a : ℕ → B) :
    IsKAutomatic k a ↔ IsKAutomaticSequence k a := by
  constructor
  · rintro ⟨hk, hfin⟩
    obtain ⟨q, ⟨e⟩⟩ := @Finite.exists_equiv_fin ↥(kKernel k a) hfin
    have hq : 0 < q :=
      Fin.pos_iff_nonempty.mpr ⟨e ⟨a, chr_self_mem_kernel a⟩⟩
    refine ⟨hk, q, hq, e ⟨a, chr_self_mem_kernel a⟩,
      fun s d => e (chr_step (e.symm s) d),
      fun s => (e.symm s).val 0, ?_⟩
    intro n ds hds
    have hfold := chr_fold_val q e
      (fun s d => e (chr_step (e.symm s) d)) (fun s d => rfl) ds
      ⟨a, chr_self_mem_kernel a⟩
    change (e.symm (ds.foldl (fun s d => e (chr_step (e.symm s) d))
      (e ⟨a, chr_self_mem_kernel a⟩))).val 0 = a n
    rw [hfold, Equiv.symm_apply_apply]
    change (⟨a, chr_self_mem_kernel a⟩ : ↥(kKernel k a)).val
      (k ^ ds.length * 0 + baseWordValueLSD ds) = a n
    rw [hds, mul_zero, zero_add]
  · rintro ⟨hk, q, hq, start, trans, out, hauto⟩
    refine ⟨hk, ?_⟩
    have hex : ∀ n, ∃ ds : List (Fin k), baseWordValueLSD ds = n :=
      fun n => chr_exists_word hk n
    choose word hword using hex
    have hfinG : (Set.range
      (fun s : Fin q => fun n : ℕ => out ((word n).foldl trans s))).Finite :=
      Set.finite_range _
    rw [Set.finite_coe_iff]
    apply hfinG.subset
    intro b hb
    obtain ⟨ee, r, hr, rfl⟩ := hb
    obtain ⟨ds_r, hlen_r, hval_r⟩ := chr_exists_word_len hk ee r hr
    refine ⟨ds_r.foldl trans start, ?_⟩
    funext n
    change out ((word n).foldl trans (ds_r.foldl trans start))
      = a (k ^ ee * n + r)
    have happend : baseWordValueLSD (ds_r ++ word n) = k ^ ee * n + r := by
      rw [chr_base_append, hword n, hval_r, hlen_r, add_comm]
    have haut := hauto (k ^ ee * n + r) (ds_r ++ word n) happend
    rw [List.foldl_append] at haut
    exact haut


end ChrAuto

end

end MetaMathlibExt
