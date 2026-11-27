/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The fluctuation theorem for currents along Schnakenberg cycles

Andrieux and Gaspard (2007): let a Markov jump process on a finite state space have transition
rates `W(ω → ω')`, with `W(ω → ω') > 0` iff `W(ω' → ω) > 0`, and an irreducible graph of allowed
transitions. Choose a spanning tree `T` of that graph; every remaining edge `l` (a chord, with a
chosen orientation `a_l → b_l`) closes a fundamental cycle `C_l` with the tree path from `b_l`
back to `a_l` (Schnakenberg 1976). The affinity of the cycle is
`𝒜_l = ln ∏_{e ∈ C_l} W(e) / W(-e)`. Let `G_l(t)` be the integrated current along chord `l` (the
number of jumps `a_l → b_l` minus the number of jumps `b_l → a_l` up to time `t`). Then the
generating function `Q(λ) = lim_{t → ∞} -(1/t) ln E[exp(-∑_l λ_l G_l(t))]` exists for every real
`λ`, does not depend on the initial state, and satisfies `Q(λ) = Q(𝒜 - λ)` (equation (39) of
arXiv:cond-mat/0512254).

Applying the Legendre transform of equation (72), `H(α) = sup_λ [Q(λ) - λ·α]`, to this symmetry
gives `H(-α) - H(α) = 𝒜·α`, the chord-current analogue of equation (73), which the source states
for grouped currents. This is an identity for the transform of `Q`, not a statement about
probabilities. Since it follows from `Q_symm` by the transform alone, it is not stated here as a
separate wanted declaration.

The expectation is written through the tilted generator, as in the source's proof: with
`L_λ(ω', ω) = W(ω → ω') exp(-∑_l λ_l s_l(ω, ω'))` for `ω' ≠ ω`, where `s_l(ω, ω')` is `+1` for the
jump `a_l → b_l`, `-1` for `b_l → a_l` and `0` otherwise, and `L_λ(ω, ω) = -∑_{ω' ≠ ω} W(ω → ω')`,
the expectation from the initial state `ω₀` is `∑_{ω'} (exp(t L_λ))(ω', ω₀)` (the Feynman–Kac
representation), which is taken as the definition. `H` is the extended-real Legendre transform
`legendreTransform` of `-Q` at `-α`, with the chords numbered by `Fin (Fintype.card ι)`;
`SchnakenbergNetwork.H_eq_iSup` gives it as the supremum above, in `[-∞, ∞]`. Not recorded here:
the version for macroscopic currents with several mechanisms (equation (69)) and the large-deviation
statement about probabilities (equations (71) and (74)), which needs the Gärtner–Ellis theorem.

Sources: D. Andrieux and P. Gaspard, "Fluctuation theorem for currents and Schnakenberg network
theory", Journal of Statistical Physics 127 (2007) 107–131, arXiv:cond-mat/0512254; equation numbers
are those of the arXiv version (v3): equations (39), (72) and (73); J. Schnakenberg, "Network
theory of microscopic and macroscopic behavior of master equation systems", Reviews of Modern
Physics 48 (1976) 571–585.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.EReal.Operations
public import MathlibExt.Probability.LegendreTransform

@[expose] public section

namespace WantedExt.Biology.Biophysics.CurrentFluctuationTheoremWanted

open Filter Topology MathlibExt.Probability.LegendreTransform
open scoped InnerProductSpace

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι]

/-- A **Schnakenberg network** for a jump process on `Ω`: rates `W ω ω'` of the jumps `ω → ω'`,
a spanning tree `T` of the graph of allowed transitions, and the oriented chords `chord l`. -/
structure SchnakenbergNetwork (Ω ι : Type*) where
  /-- The rate `W(ω → ω')`. -/
  W : Ω → Ω → ℝ
  /-- The spanning tree. -/
  T : SimpleGraph Ω
  /-- The oriented chord `a_l → b_l`. -/
  chord : ι → Ω × Ω

/-- The **standing assumptions**: rates are nonnegative, a jump is allowed iff its reverse is,
`T` is a tree all of whose edges are allowed jumps, and the chords list every allowed edge
outside `T` exactly once, with one orientation. (A tree on all of `Ω` makes the allowed graph
connected, so the process is irreducible.) -/
structure SchnakenbergNetwork.Valid (M : SchnakenbergNetwork Ω ι) : Prop where
  /-- Rates are nonnegative. -/
  nonneg : ∀ ω ω', 0 ≤ M.W ω ω'
  /-- A jump is allowed iff its reverse is. -/
  pos_iff : ∀ ω ω', ω ≠ ω' → (0 < M.W ω ω' ↔ 0 < M.W ω' ω)
  /-- `T` is a tree. -/
  isTree : M.T.IsTree
  /-- Tree edges are allowed jumps. -/
  tree_pos : ∀ ω ω', M.T.Adj ω ω' → 0 < M.W ω ω'
  /-- Chords are allowed jumps outside the tree. -/
  chord_pos : ∀ l, (M.chord l).1 ≠ (M.chord l).2 ∧ 0 < M.W (M.chord l).1 (M.chord l).2 ∧
    ¬ M.T.Adj (M.chord l).1 (M.chord l).2
  /-- Every allowed edge outside the tree is exactly one chord, in one orientation. -/
  chord_unique : ∀ ω ω', ω ≠ ω' → 0 < M.W ω ω' → ¬ M.T.Adj ω ω' →
    ∃! p : ι × Bool, M.chord p.1 = (if p.2 then (ω, ω') else (ω', ω))

/-- Given `hT : M.T.IsTree`, the unique simple path (walk) in the spanning tree `M.T` from `v` to
`w`. -/
noncomputable def SchnakenbergNetwork.treePath (M : SchnakenbergNetwork Ω ι) (hT : M.T.IsTree)
    (v w : Ω) : M.T.Walk v w :=
  (hT.existsUnique_path v w).choose

/-- The **affinity** of the fundamental cycle of chord `l = (a, b)`:
`ln (W(a → b) / W(b → a)) + ∑ ln (W(u → v) / W(v → u))` over the steps `u → v` of the tree path
from `b` back to `a`. -/
noncomputable def SchnakenbergNetwork.affinity (M : SchnakenbergNetwork Ω ι) (hT : M.T.IsTree)
    (l : ι) : ℝ :=
  Real.log (M.W (M.chord l).1 (M.chord l).2 / M.W (M.chord l).2 (M.chord l).1) +
    ((M.treePath hT (M.chord l).2 (M.chord l).1).darts.map fun d =>
      Real.log (M.W d.fst d.snd / M.W d.snd d.fst)).sum

/-- The **current increment** `s_l(ω, ω')` of chord `l` for the jump `ω → ω'`. -/
def SchnakenbergNetwork.increment (M : SchnakenbergNetwork Ω ι) (l : ι) (ω ω' : Ω) : ℝ :=
  if M.chord l = (ω, ω') then 1 else if M.chord l = (ω', ω) then -1 else 0

/-- The **tilted generator** `L_λ`, acting on column vectors indexed by states:
`L_λ(ω', ω) = W(ω → ω') exp(-∑_l λ_l s_l(ω, ω'))` for `ω' ≠ ω`, and
`L_λ(ω, ω) = -∑_{ω' ≠ ω} W(ω → ω')`. -/
noncomputable def SchnakenbergNetwork.tilted (M : SchnakenbergNetwork Ω ι) (lam : ι → ℝ) :
    Matrix Ω Ω ℝ :=
  fun ω' ω => if ω' = ω then -∑ ω'' ∈ Finset.univ.erase ω, M.W ω ω''
    else M.W ω ω' * Real.exp (-∑ l, lam l * M.increment l ω ω')

/-- The **current generating function** `E_{ω₀}[exp(-∑_l λ_l G_l(t))] = ∑_{ω'} (exp(t L_λ))(ω', ω₀)`
from the initial state `ω₀`. -/
noncomputable def SchnakenbergNetwork.genFun (M : SchnakenbergNetwork Ω ι) (lam : ι → ℝ)
    (t : ℝ) (ω₀ : Ω) : ℝ :=
  ∑ ω', NormedSpace.exp (t • M.tilted lam) ω' ω₀

/-- `Q(λ) = lim_{t → ∞} -(1/t) ln E_{ω₀}[exp(-∑_l λ_l G_l(t))]` (from any fixed initial state; its
existence and independence of the state are part of `Q_symm`). -/
noncomputable def SchnakenbergNetwork.Q (M : SchnakenbergNetwork Ω ι) (ω₀ : Ω) (lam : ι → ℝ) :
    ℝ :=
  limUnder atTop fun t : ℝ => -(1 / t) * Real.log (M.genFun lam t ω₀)

/-- **Legendre transform of `Q`.** `H(α) = Λ^*(-α)` for `Λ = -Q`, where
`Λ^*(x) = sup_y (⟨y, x⟩ - Λ(y))` is the extended-real Legendre transform on `ℝ^d`, `d = |ι|`, with
the chords numbered `0, …, d - 1`; equivalently `H(α) = sup_λ [Q(λ) - λ·α]`, in `[-∞, ∞]`. -/
noncomputable def SchnakenbergNetwork.H (M : SchnakenbergNetwork Ω ι) (ω₀ : Ω) (α : ι → ℝ) :
    EReal :=
  legendreTransform
    (fun y : EuclideanSpace ℝ (Fin (Fintype.card ι)) =>
      -((M.Q ω₀ fun l => y (Fintype.equivFin ι l) : ℝ) : EReal))
    (WithLp.toLp 2 fun i => -α ((Fintype.equivFin ι).symm i))

/-- **`H` as a supremum.** For every initial state `ω₀` and every `α`,
`H(α) = sup_λ [Q(λ) - λ·α]` in `[-∞, ∞]`, the supremum taken over all real `λ`. -/
theorem SchnakenbergNetwork.H_eq_iSup (M : SchnakenbergNetwork Ω ι) (ω₀ : Ω) (α : ι → ℝ) :
    M.H ω₀ α = ⨆ lam : ι → ℝ, ((M.Q ω₀ lam - ∑ l, lam l * α l : ℝ) : EReal) := by
  rw [SchnakenbergNetwork.H, legendreTransform_eq_iSup]
  set e := Fintype.equivFin ι
  let φ : (ι → ℝ) ≃ EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    { toFun := fun lam => WithLp.toLp 2 fun i => lam (e.symm i)
      invFun := fun y l => y (e l)
      left_inv := fun lam => by funext l; simp only [Equiv.symm_apply_apply]
      right_inv := fun y => by ext i; simp only [Equiv.apply_symm_apply] }
  rw [← φ.iSup_comp]
  congr 1
  funext lam
  have hQ : (fun l => (φ lam) (e l)) = lam := by
    funext l
    simp only [Equiv.coe_fn_mk, Equiv.symm_apply_apply, φ]
  have hinner : ⟪φ lam, WithLp.toLp 2 fun i => -α (e.symm i)⟫_ℝ = -∑ l, lam l * α l := by
    rw [PiLp.inner_apply]
    simp only [Equiv.coe_fn_mk, RCLike.inner_apply, conj_trivial, neg_mul,
      Finset.sum_neg_distrib, neg_inj, φ]
    exact (Equiv.sum_comp e.symm (fun l => α l * lam l)).trans
      (Finset.sum_congr rfl fun l _ => mul_comm _ _)
  rw [hQ, hinner, ← EReal.coe_neg, ← EReal.coe_sub]
  congr 1
  ring

/-- **Existence and symmetry of the current generating function** (Andrieux and Gaspard 2007,
equation (39) of arXiv:cond-mat/0512254): for a valid Schnakenberg network on a finite nonempty
state space with tree `T` (rates nonnegative, a jump allowed iff its reverse is, `T` a spanning tree
of allowed jumps, chords listing the remaining allowed edges once each) and every real `λ`, there is
`q` such that `-(1/t) ln E_{ω₀}[exp(-∑_l λ_l G_l(t))] → q` as `t → ∞` for every initial state `ω₀`;
and `Q(λ) = Q(𝒜 - λ)`, where `𝒜_l` is the affinity of the fundamental cycle of chord `l`.

Source: Andrieux and Gaspard (2007), arXiv:cond-mat/0512254, equation (39). -/
public theorem_wanted Q_symm [Nonempty Ω] (M : SchnakenbergNetwork Ω ι) (hM : M.Valid)
    (lam : ι → ℝ) :
    (∃ q : ℝ, ∀ ω₀, Tendsto (fun t : ℝ => -(1 / t) * Real.log (M.genFun lam t ω₀)) atTop
        (𝓝 q)) ∧
      ∀ ω₀, M.Q ω₀ lam = M.Q ω₀ (fun l => M.affinity hM.isTree l - lam l)

end WantedExt.Biology.Biophysics.CurrentFluctuationTheoremWanted
