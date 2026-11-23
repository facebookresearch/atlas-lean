/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Scattering cascades: nonexpansiveness and the energy identity

S. Mallat's windowed scattering transform (*Group invariant scattering*, Comm. Pure Appl. Math.
65 (2012), 1331–1398, arXiv:1101.2286, Section 2) iterates one layer
`U_J f = (A_J f, (U[λ] f)_{λ ∈ Λ_J})`, where `A_J f = f ⋆ φ_{2^J}` is a low-pass average and
`U[λ] f = |f ⋆ ψ_λ|` is the modulus of a wavelet coefficient. Along a path
`p = (λ₁, …, λ_m)` the **scattering propagator** is `U[p] = U[λ_m] ⋯ U[λ₁]` (Definition 2.2,
equation (15)) and the **windowed scattering** is `S_J[p] f = A_J U[p] f` (Definition 2.4).

Mallat's proofs of Proposition 2.5 (nonexpansiveness) and of the first part of Theorem 2.6 use
only two properties of one layer: it is nonexpansive,
`‖A f - A h‖² + ∑_λ ‖U[λ] f - U[λ] h‖² ≤ ‖f - h‖²`, and it preserves the norm,
`‖A f‖² + ∑_λ ‖U[λ] f‖² = ‖f‖²` (Proposition 2.1 and the nonexpansiveness of the modulus give
both for the wavelet layer). This file proves those structural results for an **arbitrary**
layer with these properties: the index set `Λ` may be infinite and the maps `U[λ]` nonlinear.
Squared distances and norms are taken in `ℝ≥0∞` (`edist`, `‖·‖ₑ`), so that sums over infinitely
many paths need no summability side conditions.

## Main declarations

* `propagator U p` : `U[p]` for a path `p : Fin m → Λ`, applying `U (p 0)` first.
* `sum_edist_sq_le` : for every depth `m`,
  `∑_{n<m} ∑_{|p|=n} ‖A U[p] f - A U[p] h‖² + ∑_{|p|=m} ‖U[p] f - U[p] h‖² ≤ ‖f - h‖²`
  (the inequality chain in the proof of Proposition 2.5).
* `tsum_edist_sq_le` : Proposition 2.5, `‖S_J[P_J] f - S_J[P_J] h‖ ≤ ‖f - h‖` over all finite
  paths (equations (27)–(28)).
* `sum_enorm_sq_eq` : the energy identity
  `‖f‖² = ∑_{n<m} ∑_{|p|=n} ‖A U[p] f‖² + ∑_{|p|=m} ‖U[p] f‖²` (equation (34)).
* `tsum_enorm_sq_eq_iff_tendsto` : the scattering preserves the norm,
  `∑_p ‖A U[p] f‖² = ‖f‖²`, if and only if the energy `∑_{|p|=m} ‖U[p] f‖²` propagated to depth
  `m` tends to `0` (the first step of the proof of Theorem 2.6).

That the propagated energy does tend to `0` for admissible wavelets (Theorem 2.6, condition (30))
is analytic and is recorded in `WantedExt`.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace MathlibExt.Analysis.Wavelet.ScatteringCascade

variable {X Λ : Type*}

/-- **Scattering propagator** along a path (S. Mallat, *Group invariant scattering*, Comm. Pure
Appl. Math. 65 (2012), Definition 2.2, equation (15)). For maps `U : Λ → X → X` and a path
`p = (p 0, …, p (m-1))`, `propagator U p = U (p (m-1)) ∘ ⋯ ∘ U (p 0)`, with the empty path
giving the identity: the first index of the path is applied first, so that `U[p + p'] =
U[p'] U[p]` (equation (17)). -/
def propagator (U : Λ → X → X) : {m : ℕ} → (Fin m → Λ) → X → X
  | 0, _ => id
  | _ + 1, p => propagator U (Fin.tail p) ∘ U (p 0)

@[simp]
theorem propagator_zero (U : Λ → X → X) (p : Fin 0 → Λ) : propagator U p = id := rfl

@[simp]
theorem propagator_cons (U : Λ → X → X) {m : ℕ} (l : Λ) (q : Fin m → Λ) (x : X) :
    propagator U (Fin.cons l q : Fin (m + 1) → Λ) x = propagator U q (U l x) := by
  simp [propagator]

/-- **Sums over paths split along the first index.** A sum over the paths of length `m + 1`
is the sum over the first index of the sums over the remaining paths of length `m`. -/
theorem tsum_paths_succ {m : ℕ} (g : (Fin (m + 1) → Λ) → ℝ≥0∞) :
    ∑' p : Fin (m + 1) → Λ, g p = ∑' (l : Λ) (q : Fin m → Λ), g (Fin.cons l q) := by
  rw [← (Fin.consEquiv fun _ => Λ).tsum_eq, ← ENNReal.tsum_prod]
  rfl

/-- **Cascade inequality.** On an abstract state space, if `a x + ∑_λ c (u λ x) ≤ c x` for
every `x`, then `∑_{n<m} ∑_{|p|=n} a (u[p] x) + ∑_{|p|=m} c (u[p] x) ≤ c x` for every depth
`m`: the one-layer bound propagates through any number of layers. -/
theorem cascade_le (a c : X → ℝ≥0∞) (u : Λ → X → X)
    (h : ∀ x, a x + ∑' l, c (u l x) ≤ c x) (m : ℕ) (x : X) :
    ∑ n ∈ Finset.range m, ∑' p : Fin n → Λ, a (propagator u p x) +
      ∑' p : Fin m → Λ, c (propagator u p x) ≤ c x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    calc ∑ n ∈ Finset.range (m + 1), ∑' p : Fin n → Λ, a (propagator u p x) +
          ∑' p : Fin (m + 1) → Λ, c (propagator u p x)
        = a x + ∑' l, (∑ n ∈ Finset.range m, ∑' p : Fin n → Λ, a (propagator u p (u l x)) +
            ∑' p : Fin m → Λ, c (propagator u p (u l x))) := by
          have h0 : ∑' p : Fin 0 → Λ, a (propagator u p x) = a x := by simp [tsum_fintype]
          have h1 : ∀ n, ∑' p : Fin (n + 1) → Λ, a (propagator u p x) =
              ∑' (l : Λ) (q : Fin n → Λ), a (propagator u q (u l x)) := fun n => by
            rw [tsum_paths_succ]; simp only [propagator_cons]
          have h2 : ∑' p : Fin (m + 1) → Λ, c (propagator u p x) =
              ∑' (l : Λ) (q : Fin m → Λ), c (propagator u q (u l x)) := by
            rw [tsum_paths_succ]; simp only [propagator_cons]
          rw [Finset.sum_range_succ', h0, h2, ENNReal.tsum_add,
            Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          simp only [h1]
          ring
      _ ≤ a x + ∑' l, c (u l x) := by gcongr with l; exact ih (u l x)
      _ ≤ c x := h x

/-- **Cascade identity.** On an abstract state space, if `a x + ∑_λ c (u λ x) = c x` for every
`x`, then `∑_{n<m} ∑_{|p|=n} a (u[p] x) + ∑_{|p|=m} c (u[p] x) = c x` for every depth `m`. -/
theorem cascade_eq (a c : X → ℝ≥0∞) (u : Λ → X → X)
    (h : ∀ x, a x + ∑' l, c (u l x) = c x) (m : ℕ) (x : X) :
    ∑ n ∈ Finset.range m, ∑' p : Fin n → Λ, a (propagator u p x) +
      ∑' p : Fin m → Λ, c (propagator u p x) = c x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    calc ∑ n ∈ Finset.range (m + 1), ∑' p : Fin n → Λ, a (propagator u p x) +
          ∑' p : Fin (m + 1) → Λ, c (propagator u p x)
        = a x + ∑' l, (∑ n ∈ Finset.range m, ∑' p : Fin n → Λ, a (propagator u p (u l x)) +
            ∑' p : Fin m → Λ, c (propagator u p (u l x))) := by
          have h0 : ∑' p : Fin 0 → Λ, a (propagator u p x) = a x := by simp [tsum_fintype]
          have h1 : ∀ n, ∑' p : Fin (n + 1) → Λ, a (propagator u p x) =
              ∑' (l : Λ) (q : Fin n → Λ), a (propagator u q (u l x)) := fun n => by
            rw [tsum_paths_succ]; simp only [propagator_cons]
          have h2 : ∑' p : Fin (m + 1) → Λ, c (propagator u p x) =
              ∑' (l : Λ) (q : Fin m → Λ), c (propagator u q (u l x)) := by
            rw [tsum_paths_succ]; simp only [propagator_cons]
          rw [Finset.sum_range_succ', h0, h2, ENNReal.tsum_add,
            Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          simp only [h1]
          ring
      _ = a x + ∑' l, c (u l x) := by simp only [ih]
      _ = c x := h x

section Metric

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]

/-- **Nonexpansiveness of a scattering cascade at every depth** (S. Mallat, *Group invariant
scattering*, Comm. Pure Appl. Math. 65 (2012), proof of Proposition 2.5). Let one layer
`f ↦ (A f, (U λ f)_{λ ∈ Λ})` be nonexpansive:
`‖A f - A h‖² + ∑_λ ‖U λ f - U λ h‖² ≤ ‖f - h‖²`. Then for every depth `m`,
`∑_{n<m} ∑_{|p|=n} ‖A U[p] f - A U[p] h‖² + ∑_{|p|=m} ‖U[p] f - U[p] h‖² ≤ ‖f - h‖²`,
where `U[p]` is the `propagator`. -/
theorem sum_edist_sq_le (A : E → F) (U : Λ → E → E)
    (hlayer : ∀ f h, edist (A f) (A h) ^ 2 + ∑' l, edist (U l f) (U l h) ^ 2 ≤ edist f h ^ 2)
    (m : ℕ) (f h : E) :
    ∑ n ∈ Finset.range m, ∑' p : Fin n → Λ,
        edist (A (propagator U p f)) (A (propagator U p h)) ^ 2 +
      ∑' p : Fin m → Λ, edist (propagator U p f) (propagator U p h) ^ 2 ≤ edist f h ^ 2 := by
  have key := cascade_le (X := E × E) (fun x => edist (A x.1) (A x.2) ^ 2)
    (fun x => edist x.1 x.2 ^ 2) (fun l x => (U l x.1, U l x.2))
    (fun x => hlayer x.1 x.2) m (f, h)
  have hprop : ∀ {n} (p : Fin n → Λ) (x : E × E),
      propagator (fun l (x : E × E) => (U l x.1, U l x.2)) p x =
        (propagator U p x.1, propagator U p x.2) := by
    intro n
    induction n with
    | zero => intro p x; rfl
    | succ n ih =>
      intro p x
      rw [← Fin.cons_self_tail p, propagator_cons, propagator_cons, propagator_cons, ih]
  simpa only [hprop] using key

/-- **The windowed scattering transform is nonexpansive** (S. Mallat, *Group invariant
scattering*, Comm. Pure Appl. Math. 65 (2012), Proposition 2.5, equations (27)–(28)). If one
layer `f ↦ (A f, (U λ f)_{λ ∈ Λ})` is nonexpansive, then summing over all finite paths `p`,
`∑_p ‖A U[p] f - A U[p] h‖² ≤ ‖f - h‖²`; that is,
`‖S_J[P_J] f - S_J[P_J] h‖ ≤ ‖f - h‖` with `S_J[p] = A U[p]`. -/
theorem tsum_edist_sq_le (A : E → F) (U : Λ → E → E)
    (hlayer : ∀ f h, edist (A f) (A h) ^ 2 + ∑' l, edist (U l f) (U l h) ^ 2 ≤ edist f h ^ 2)
    (f h : E) :
    ∑' p : (Σ n, Fin n → Λ), edist (A (propagator U p.2 f)) (A (propagator U p.2 h)) ^ 2 ≤
      edist f h ^ 2 := by
  rw [ENNReal.tsum_sigma', ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun m =>
    le_trans le_self_add (sum_edist_sq_le A U hlayer m f h)

end Metric

section Norm

variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- **Energy identity of a scattering cascade** (S. Mallat, *Group invariant scattering*, Comm.
Pure Appl. Math. 65 (2012), proof of Theorem 2.6, equations (33)–(34)). Let one layer preserve
the norm: `‖A f‖² + ∑_λ ‖U λ f‖² = ‖f‖²`. Then for every depth `m`,
`‖f‖² = ∑_{n<m} ∑_{|p|=n} ‖A U[p] f‖² + ∑_{|p|=m} ‖U[p] f‖²`: the energy of `f` splits into
the scattering coefficients of order `< m` and the energy propagated to depth `m`. -/
theorem sum_enorm_sq_eq (A : E → F) (U : Λ → E → E)
    (hlayer : ∀ f, ‖A f‖ₑ ^ 2 + ∑' l, ‖U l f‖ₑ ^ 2 = ‖f‖ₑ ^ 2) (m : ℕ) (f : E) :
    ∑ n ∈ Finset.range m, ∑' p : Fin n → Λ, ‖A (propagator U p f)‖ₑ ^ 2 +
      ∑' p : Fin m → Λ, ‖propagator U p f‖ₑ ^ 2 = ‖f‖ₑ ^ 2 :=
  cascade_eq (fun x => ‖A x‖ₑ ^ 2) (fun x => ‖x‖ₑ ^ 2) U hlayer m f

/-- **Norm preservation is equivalent to the decay of the propagated energy** (S. Mallat,
*Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), first paragraph of the proof of
Theorem 2.6). If one layer preserves the norm, `‖A f‖² + ∑_λ ‖U λ f‖² = ‖f‖²`, then the
scattering over all finite paths preserves the norm of `f`,
`∑_p ‖A U[p] f‖² = ‖f‖²` (equation (32)), if and only if the energy propagated to depth `m`,
`∑_{|p|=m} ‖U[p] f‖²`, tends to `0` as `m → ∞` (equation (31)). -/
theorem tsum_enorm_sq_eq_iff_tendsto (A : E → F) (U : Λ → E → E)
    (hlayer : ∀ f, ‖A f‖ₑ ^ 2 + ∑' l, ‖U l f‖ₑ ^ 2 = ‖f‖ₑ ^ 2) (f : E) :
    ∑' p : (Σ n, Fin n → Λ), ‖A (propagator U p.2 f)‖ₑ ^ 2 = ‖f‖ₑ ^ 2 ↔
      Tendsto (fun m => ∑' p : Fin m → Λ, ‖propagator U p f‖ₑ ^ 2) atTop (𝓝 0) := by
  set s : ℕ → ℝ≥0∞ := fun m =>
    ∑ n ∈ Finset.range m, ∑' p : Fin n → Λ, ‖A (propagator U p f)‖ₑ ^ 2
  set r : ℕ → ℝ≥0∞ := fun m => ∑' p : Fin m → Λ, ‖propagator U p f‖ₑ ^ 2
  have hsr : ∀ m, s m + r m = ‖f‖ₑ ^ 2 := fun m => sum_enorm_sq_eq A U hlayer m f
  have hfin : ‖f‖ₑ ^ 2 ≠ ∞ := by simp
  have hr : ∀ m, r m = ‖f‖ₑ ^ 2 - s m := fun m =>
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top hfin (le_self_add.trans (hsr m).le))
      ((add_comm _ _).trans (hsr m))
  have hs : ∀ m, s m = ‖f‖ₑ ^ 2 - r m := fun m =>
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top hfin (le_add_self.trans (hsr m).le)) (hsr m)
  have hmono : Monotone s := fun m n hmn =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hmn)
  have htot : ∑' p : (Σ n, Fin n → Λ), ‖A (propagator U p.2 f)‖ₑ ^ 2 = ⨆ m, s m := by
    rw [ENNReal.tsum_sigma', ENNReal.tsum_eq_iSup_nat]
  have hlim : Tendsto s atTop (𝓝 (⨆ m, s m)) := tendsto_atTop_iSup hmono
  rw [htot]
  constructor
  · intro heq
    rw [heq] at hlim
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := ‖f‖ₑ ^ 2)) hlim (Or.inl hfin)
    simpa [← hr] using this
  · intro hr0
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := ‖f‖ₑ ^ 2)) hr0 (Or.inl hfin)
    simp only [tsub_zero, ← hs] at this
    exact tendsto_nhds_unique hlim this

end Norm

end MathlibExt.Analysis.Wavelet.ScatteringCascade
