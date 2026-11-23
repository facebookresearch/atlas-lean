/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainConstruction
public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Kernel.Basic

/-!
# Markov chain path measure

The canonical law on path space `ℕ → S` of a Markov chain with initial
distribution `μ` and transition kernel `κ`, built from Mathlib's
Ionescu--Tulcea trajectory measure, together with the key shift
identity: the integral of a path functional composed with the time-`n`
shift against the trajectory measure started from a history `x₀`
depends only on the last coordinate of `x₀`.

## Source

This formalizes `v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean`
(`MarkovChainPathMeasure`, `markovExpectation`,
`measurable_markovExpectation`, `integral_shiftPath_traj_eq_markovExpectation`)
and the path-filtration / shift definitions it uses. The target is the
book's "Theorem (Markov property)" and "Theorem (Strong Markov property)"
(Lecture 31): the Markov and strong Markov properties for chains are
proved in the companion modules
`MathlibExt.Probability.MarkovPropertyChain` and
`MathlibExt.Probability.StrongMarkovChain`.

## Audit note

In v1, `integral_shiftPath_traj_eq_markovExpectation` is left unproved,
and the Markov and strong Markov properties for chains
rest on it; batch 31 (Markov chain construction) explicitly left those
two properties out for this reason. The proof here is new, not a port:
finite-dimensional distributions of the shifted trajectory are shown
to depend only on the last coordinate of the initial history
(`partialTraj_map_drop`, by induction on the number of dropped
coordinates, using the one-step shift `partialTraj_succ_map_drop`),
and the two trajectory measures are identified by uniqueness of
projective limits.

## Canonical construction

The lifted kernel and path measure reuse
`MathlibExt.Probability.MarkovChainConstruction`. Compatibility abbreviations
preserve the names and argument order used by the existing Markov-property
statements. Kernel/probability instances come from that module; this file adds
the finite-measure instance needed for a finite initial measure.
`pathFiltration`, `shiftPath`, and `markovExpectation` are supporting interfaces
for the shifted-trajectory identities here.

## Main results

* `MathlibExt.Probability.MarkovChainPath.markovLiftKernel`:
  the kernel `κ` lifted to finite histories, reading off the last
  coordinate.
* `MathlibExt.Probability.MarkovChainPath.pathFiltration`:
  the canonical filtration on path space `ℕ → S`.
* `MathlibExt.Probability.MarkovChainPath.MarkovChainPathMeasure`:
  the canonical measure `P_μ` on path space.
* `MathlibExt.Probability.MarkovChainPath.markovExpectation`:
  `E_x Y`, the expectation of a path functional under the chain
  started from `x`, and its measurability in `x`.
* `MathlibExt.Probability.MarkovChainPath.integral_shiftPath_traj_eq_markovExpectation`:
  the shifted-trajectory integral identity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Kernel Finset

namespace MathlibExt.Probability.MarkovChainPath

noncomputable section

variable {S : Type*} [MeasurableSpace S]

lemma piSingleton_apply (a : ℕ) (x : S) (j : ↥(Finset.Ioc a (a + 1))) :
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) a) x j = x := by
  obtain ⟨jval, hj⟩ := j
  rw [Finset.mem_Ioc] at hj
  obtain rfl : jval = a + 1 := by omega
  simp [MeasurableEquiv.piSingleton]

lemma piSingleton_symm_apply (a : ℕ) (t : ↥(Finset.Ioc a (a + 1)) → S) :
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) a).symm t
      = t ⟨a + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩⟩ := rfl

def dropHist (a b : ℕ) : (Π _i : ↥(Finset.Iic (a + b)), S) → (Π _i : ↥(Finset.Iic b), S) :=
  fun z i => z ⟨a + i, Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) a)⟩

lemma measurable_dropHist (a b : ℕ) : Measurable (dropHist (S := S) a b) := by
  apply Measurable.of_eval; intro i
  exact measurable_pi_apply (⟨a + i, Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) a)⟩ : ↥(Finset.Iic (a + b)))

def reindexIoc (a b : ℕ) :
    (Π _i : ↥(Finset.Ioc (a + b) (a + b + 1)), S) → (Π _i : ↥(Finset.Ioc b (b + 1)), S) :=
  (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b) ∘ (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (a + b)).symm

lemma measurable_reindexIoc (a b : ℕ) : Measurable (reindexIoc (S := S) a b) :=
  (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b).measurable.comp (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (a + b)).symm.measurable

lemma reindexIoc_comp_piSingleton (a b : ℕ) :
    (reindexIoc (S := S) a b) ∘ (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (a + b))
      = (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b) := by
  funext y
  simp [reindexIoc]

lemma dropHist_comp_IicProdIoc (a b : ℕ) :
    (dropHist (S := S) a (b + 1)) ∘ (IicProdIoc (X := fun _ : ℕ => S) (a + b) (a + b + 1))
    = (IicProdIoc (X := fun _ : ℕ => S) b (b + 1)) ∘ (Prod.map (dropHist a b) (reindexIoc a b)) := by
  funext p i
  obtain ⟨p1, p2⟩ := p
  have hmap1 : (Prod.map (dropHist (S := S) a b) (reindexIoc a b) (p1, p2)).1 = dropHist a b p1 := rfl
  have hmap2 : (Prod.map (dropHist (S := S) a b) (reindexIoc a b) (p1, p2)).2 = reindexIoc a b p2 := rfl
  simp only [Function.comp_apply, IicProdIoc, dropHist, hmap1, hmap2]
  split_ifs with h1 h2 h3
  · rfl
  · omega
  · omega
  · have hi : (i : ℕ) = b + 1 := by
      have := i.2; rw [Finset.mem_Iic] at this; omega
    simp only [Function.comp_apply, reindexIoc, piSingleton_apply, piSingleton_symm_apply]
    congr 1
    apply Subtype.ext
    show a + (i : ℕ) = a + b + 1
    omega

/-- **Lifted transition kernel on histories.** For a kernel $\kappa$ on $S$ and $n \in \mathbb{N}$,
this is the kernel from histories $(x_0, \dots, x_n)$ of states in $S$, indexed by
$\{0, \dots, n\}$, to $S$ that sends $(x_0, \dots, x_n)$ to $\kappa(x_n, \cdot)$. It is the
Markov lift kernel of $\kappa$ at $n$. -/
noncomputable abbrev markovLiftKernel (κ : Kernel S S) (n : ℕ) :
    Kernel ((_i : ↥(Finset.Iic n)) → S) S :=
  MathlibExt.Probability.MarkovChainConstruction.markovLiftKernel κ n

variable (κ : Kernel S S) [IsMarkovKernel κ]

omit [IsMarkovKernel κ] in
lemma markovLiftKernel_apply {n : ℕ} (z : Π _i : ↥(Finset.Iic n), S) :
    markovLiftKernel κ n z = κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := rfl

omit [MeasurableSpace S] in
lemma dropHist_last (a b : ℕ) (z : Π _i : ↥(Finset.Iic (a + b)), S) :
    (dropHist a b z) ⟨b, Finset.mem_Iic.mpr le_rfl⟩ = z ⟨a + b, Finset.mem_Iic.mpr le_rfl⟩ := rfl

/-- **One-step shift of a Markov partial trajectory.** Let $\kappa$ be a Markov kernel on a
measurable space $S$, let $a, b \in \mathbb{N}$ and let $z = (z_0, \dots, z_{a+b})$ be a history
in $S^{\{0, \dots, a+b\}}$. Let $\mu_z$ be the one-step partial trajectory of the lifted kernel
of $\kappa$ from time $a + b$ to time $a + b + 1$ started at $z$, that is, the law of
$(z_0, \dots, z_{a+b}, X)$ where $X$ has law $\kappa(z_{a+b})$. Then the image of $\mu_z$ under
the map $(y_0, \dots, y_{a+b+1}) \mapsto (y_a, \dots, y_{a+b+1})$ that drops the first $a$
coordinates equals the one-step partial trajectory of the lifted kernel from time $b$ to time
$b + 1$ started at $(z_a, \dots, z_{a+b})$, that is, the law of $(z_a, \dots, z_{a+b}, X')$ where
$X'$ has law $\kappa(z_{a+b})$. -/
theorem partialTraj_succ_map_drop {a b : ℕ} (z : Π _i : ↥(Finset.Iic (a + b)), S) :
    ((partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) (a + b) (a + b + 1)) z).map (dropHist a (b + 1))
    = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) b (b + 1) (dropHist a b z) := by
  have hmap : ∀ (m : ℕ) (η : Kernel (Π _i : ↥(Finset.Iic m), S) ((Π _i : ↥(Finset.Iic m), S) × (Π _i : ↥(Finset.Ioc m (m + 1)), S))) (w : Π _i : ↥(Finset.Iic m), S),
      (η.map (IicProdIoc (X := fun _ : ℕ => S) m (m + 1))) w
        = (η w).map (IicProdIoc (X := fun _ : ℕ => S) m (m + 1)) := by
    intro m η w
    exact Kernel.map_apply η measurable_IicProdIoc w
  have hη : ∀ (m : ℕ) (w : Π _i : ↥(Finset.Iic m), S),
      ((markovLiftKernel κ m).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m)) w
        = (κ (w ⟨m, Finset.mem_Iic.mpr le_rfl⟩)).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m) := by
    intro m w
    exact Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m).measurable w |>.trans (by rw [markovLiftKernel_apply])
  rw [partialTraj_succ_self, partialTraj_succ_self, hmap, hmap,
    Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply, Kernel.id_apply,
    Measure.map_map (measurable_dropHist a (b + 1)) measurable_IicProdIoc,
    dropHist_comp_IicProdIoc,
    ← Measure.map_map (g := IicProdIoc (X := fun _ : ℕ => S) b (b + 1)) (f := Prod.map (dropHist a b) (reindexIoc a b)) measurable_IicProdIoc ((measurable_dropHist a b).prodMap (measurable_reindexIoc a b)),
    ← Measure.map_prod_map _ _ (measurable_dropHist a b) (measurable_reindexIoc a b),
    Measure.map_dirac' (measurable_dropHist a b)]
  congr 1
  rw [hη, hη,
    Measure.map_map (measurable_reindexIoc a b) (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) (a + b)).measurable,
    reindexIoc_comp_piSingleton, dropHist_last]

/-- **Last-coordinate history.** For $a \in \mathbb{N}$ and a history $x = (x_0, \dots, x_a)$ of
states in $S$, indexed by $\{0, \dots, a\}$, the last-coordinate history of $x$ is the history
indexed by $\{0\}$ whose only entry is $x_a$. -/
def lastHist (a : ℕ) (x₀ : Π _i : ↥(Finset.Iic a), S) : Π _i : ↥(Finset.Iic 0), S :=
  fun _i => x₀ ⟨a, Finset.mem_Iic.mpr le_rfl⟩

lemma measurable_lastHist (a : ℕ) : Measurable (lastHist (S := S) a) := by
  apply Measurable.of_eval; intro i
  exact measurable_pi_apply (⟨a, Finset.mem_Iic.mpr le_rfl⟩ : ↥(Finset.Iic a))

/-- **One-step shift of the partial trajectory kernel.** Let $\kappa$ be a Markov kernel on $S$
and $a, b \in \mathbb{N}$. For a history $z = (z_0, \dots, z_{a+b})$ of states in $S$, extend
$z$ by one step, drawing $z_{a+b+1}$ from $\kappa(z_{a+b}, \cdot)$, and then keep the entries
at times $a, \dots, a + b + 1$, reindexed as $0, \dots, b + 1$. The law of the result equals
the law obtained by first keeping the entries of $z$ at times $a, \dots, a + b$, reindexed as
$0, \dots, b$, and then extending that history by one step in the same way. This holds as an
identity of kernels in $z$. -/
theorem partialTraj_succ_map_drop_kernel {a b : ℕ} :
    (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) (a + b) (a + b + 1)).map (dropHist a (b + 1))
      = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) b (b + 1) ∘ₖ
          Kernel.deterministic (dropHist (S := S) a b) (measurable_dropHist a b) := by
  apply Kernel.ext
  intro z
  have hL : ((partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) (a + b) (a + b + 1)).map (dropHist a (b + 1))) z
      = (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) (a + b) (a + b + 1) z).map (dropHist a (b + 1)) :=
    Kernel.map_apply _ (measurable_dropHist a (b + 1)) z
  have hR : (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) b (b + 1) ∘ₖ
      Kernel.deterministic (dropHist (S := S) a b) (measurable_dropHist a b)) z
      = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) b (b + 1) (dropHist a b z) := by
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  rw [hL, hR]
  exact partialTraj_succ_map_drop κ z

/-- **Shifted finite-dimensional distributions.** Let $\kappa$ be a Markov kernel on $S$ and
$a, b \in \mathbb{N}$. For a history $x = (x_0, \dots, x_a)$ of states in $S$, let $Q_x$ be the
law of the history $(X_0, \dots, X_{a+b})$ that equals $x$ at times $0, \dots, a$ and then draws
each next state from $\kappa$ applied to the current state (the Ionescu–Tulcea partial
trajectory from time $a$ to time $a + b$). Then the image of $Q_x$ under
$(X_0, \dots, X_{a+b}) \mapsto (X_a, \dots, X_{a+b})$, with the times reindexed as
$0, \dots, b$, equals the law of $(X_0, \dots, X_b)$ under the partial trajectory from time $0$
to time $b$ started from the one-entry history $(x_a)$. This holds as an identity of kernels
in $x$. -/
theorem partialTraj_map_drop {a b : ℕ} :
    (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) a (a + b)).map (dropHist a b)
      = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b ∘ₖ
          Kernel.deterministic (lastHist (S := S) a) (measurable_lastHist a) := by
  induction b with
  | zero =>
    apply Kernel.ext
    intro z
    have hL : ((partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) a (a + 0)).map (dropHist a 0)) z
        = (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) a (a + 0) z).map (dropHist a 0) :=
      Kernel.map_apply _ (measurable_dropHist a 0) z
    have hR : (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 0 ∘ₖ
        Kernel.deterministic (lastHist (S := S) a) (measurable_lastHist a)) z
        = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 0 (lastHist a z) := by
      rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
    rw [hL, hR]
    simp only [Nat.add_zero, partialTraj_self, Kernel.id_apply]
    rw [Measure.map_dirac' (measurable_dropHist a 0)]
    congr 1
    funext i
    obtain ⟨ival, hi⟩ := i
    rw [Finset.mem_Iic] at hi
    have : ival = 0 := by omega
    subst this
    rfl
  | succ b ih =>
    show (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) a (a + b + 1)).map (dropHist a (b + 1))
      = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 (b + 1) ∘ₖ
          Kernel.deterministic (lastHist (S := S) a) (measurable_lastHist a)
    rw [partialTraj_succ_eq_comp (Nat.le_add_right a b)]
    rw [Kernel.map_comp]
    rw [partialTraj_succ_map_drop_kernel κ]
    rw [Kernel.comp_assoc]
    rw [Kernel.deterministic_comp_eq_map (measurable_dropHist a b)]
    rw [ih]
    rw [← Kernel.comp_assoc]
    rw [partialTraj_comp_partialTraj (Nat.zero_le b) (Nat.le_succ b)]

/-- **Time shift on path space.** Let $S$ be a set and $n \in \mathbb{N}$. The time-$n$ shift on
the path space $S^{\mathbb{N}}$ sends a path $\omega$ to the path $k \mapsto \omega_{n+k}$. -/
def shiftPath (n : ℕ) : (ℕ → S) → (ℕ → S) :=
  fun ω k => ω (n + k)

lemma measurable_shiftPath (n : ℕ) : Measurable (shiftPath (S := S) n) := by
  apply Measurable.of_eval; intro k
  exact measurable_pi_apply (n + k)

omit [MeasurableSpace S] in
/-- **Finite restrictions of the shifted path.** For all $n, b \in \mathbb{N}$ and every path
$\omega : \mathbb{N} \to S$, let $\theta_n \omega$ be the shifted path, $(\theta_n \omega)_k =
\omega_{n+k}$. The restriction of $\theta_n \omega$ to the times $0, \dots, b$ equals the
restriction of $\omega$ to the times $0, \dots, n + b$ with its entries at times $n, \dots, n + b$
kept and reindexed as $0, \dots, b$; that is, it is the tuple
$(\omega_n, \omega_{n+1}, \dots, \omega_{n+b})$. -/
lemma frestrictLe_comp_shiftPath (n b : ℕ) :
    (Preorder.frestrictLe (π := fun _ : ℕ => S) b) ∘ (shiftPath (S := S) n)
      = (dropHist n b) ∘ (Preorder.frestrictLe (π := fun _ : ℕ => S) (n + b)) := by
  funext ω i
  rfl

/-- **The shifted trajectory of a Markov chain restarts from its last state.** Let $\kappa$ be a
Markov kernel on a measurable space $S$, let $n \in \mathbb{N}$ and let
$x = (x_0, \dots, x_n) \in S^{\{0, \dots, n\}}$. Let $P_x$ be the trajectory measure on
$S^{\mathbb{N}}$ of the lifted kernel of $\kappa$ started at time $n$ from the history $x$, and
let $P_{x_n}$ be the trajectory measure of the lifted kernel started at time $0$ from the
one-point history $x_n$. Then the image of $P_x$ under the time-$n$ shift
$\omega \mapsto (k \mapsto \omega_{n+k})$ equals $P_{x_n}$. -/
theorem traj_map_shiftPath_eq {n : ℕ} (x₀ : Π _i : ↥(Finset.Iic n), S) :
    (Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) n x₀).map (shiftPath n)
      = Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 (lastHist n x₀) := by
  have hfam : IsProjectiveMeasureFamily (α := fun _ : ℕ => S)
      (inducedFamily (X := fun _ : ℕ => S) (fun b => partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀))) :=
    isProjectiveMeasureFamily_partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) (lastHist n x₀)
  have hM : IsProjectiveLimit
      ((Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) n x₀).map (shiftPath n))
      (inducedFamily (X := fun _ : ℕ => S) (fun b => partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀))) := by
    rw [isProjectiveLimit_nat_iff hfam]
    intro b
    have hFDDx : (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) n (n + b) x₀).map (dropHist n b)
        = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀) := by
      have h := partialTraj_map_drop (κ) (a := n) (b := b)
      have h1 : ((partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) n (n + b)).map (dropHist n b)) x₀
          = (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) n (n + b) x₀).map (dropHist n b) :=
        Kernel.map_apply _ (measurable_dropHist n b) x₀
      have h2 : (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b ∘ₖ
          Kernel.deterministic (lastHist (S := S) n) (measurable_lastHist n)) x₀
          = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀) := by
        rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
      rw [← h1, h, h2]
    calc ((Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) n x₀).map (shiftPath n)).map
            (Preorder.frestrictLe (π := fun _ : ℕ => S) b)
        = (Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) n x₀).map
            ((Preorder.frestrictLe (π := fun _ : ℕ => S) b) ∘ (shiftPath n)) := by
          rw [Measure.map_map (Preorder.measurable_frestrictLe b) (measurable_shiftPath n)]
      _ = (Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) n x₀).map
            ((dropHist n b) ∘ (Preorder.frestrictLe (π := fun _ : ℕ => S) (n + b))) := by
          rw [frestrictLe_comp_shiftPath]
      _ = ((Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) n x₀).map
            (Preorder.frestrictLe (π := fun _ : ℕ => S) (n + b))).map (dropHist n b) := by
          rw [Measure.map_map (measurable_dropHist n b) (Preorder.measurable_frestrictLe (n + b))]
      _ = (partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) n (n + b) x₀).map (dropHist n b) := by
          rw [traj_map_frestrictLe_apply]
      _ = partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀) := hFDDx
      _ = inducedFamily (X := fun _ : ℕ => S) (fun b => partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀)) (Finset.Iic b) := by
          rw [inducedFamily_Iic]
  have hT : IsProjectiveLimit
      (Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 (lastHist n x₀))
      (inducedFamily (X := fun _ : ℕ => S) (fun b => partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀))) := by
    rw [Kernel.traj_apply]
    exact isProjectiveLimit_trajFun (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 (lastHist n x₀)
  have : ∀ (i : Finset ℕ), IsFiniteMeasure
      (inducedFamily (X := fun _ : ℕ => S) (fun b => partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀)) i) := by
    intro i
    show IsFiniteMeasure (((fun b => partialTraj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 b (lastHist n x₀)) (i.sup id)).map
      (restrict₂ (π := fun _ : ℕ => S) i.subset_Iic_sup_id))
    infer_instance
  exact (hT.unique hM).symm


/-- **Path filtration.** Let $S$ be a measurable space. The path filtration on the path space
$S^{\mathbb{N}}$ is the filtration indexed by $\mathbb{N}$, relative to the product σ-algebra,
whose σ-algebra at time $n$ is the one generated by the coordinate maps $\omega \mapsto \omega_i$
for $i \le n$. -/
noncomputable def pathFiltration (S : Type*) [MeasurableSpace S] :
    Filtration ℕ
      (m := MeasurableSpace.pi (m := fun _ : ℕ => (inferInstance : MeasurableSpace S))) where
  seq n := ⨆ (i : ℕ) (_ : i ≤ n),
    MeasurableSpace.comap (fun (ω : ℕ → S) => ω i) ‹MeasurableSpace S›
  mono' i j hij := iSup_mono fun k => iSup_mono' fun hk => ⟨hk.trans hij, le_rfl⟩
  le' n := iSup_le fun k => iSup_le fun _ => (measurable_pi_apply k).comap_le

/-- **The path filtration is contained in the product σ-algebra.** Let $S$ be a measurable space.
For every $n \in \mathbb{N}$, the $n$-th σ-algebra of the path filtration on $S^{\mathbb{N}}$,
generated by the coordinate maps $\omega \mapsto \omega_i$ for $i \le n$, is contained in the
product σ-algebra on $S^{\mathbb{N}}$. -/
lemma pathFiltration_le_pi (S : Type*) [MeasurableSpace S] (n : ℕ) :
    pathFiltration S n ≤ MeasurableSpace.pi := by
  exact (pathFiltration S).le' n

/-- **Markov chain path measure.** For a measure $\mu$ on $S$ and a Markov kernel $\kappa$ on
$S$, the path measure $P_\mu$ is the measure on $S^{\mathbb{N}}$, with the product
$\sigma$-algebra, obtained by integrating against $\mu(dx)$ the Ionescu–Tulcea trajectory
measure that starts at $x$ at time $0$ and draws each next state from $\kappa$ applied to the
current state. It is the Markov chain measure of $\kappa$ and $\mu$; when $\mu$ is a
probability measure it is the law on path space of the Markov chain with initial distribution
$\mu$ and transition kernel $\kappa$. -/
noncomputable abbrev MarkovChainPathMeasure
    (S : Type*) [MeasurableSpace S]
    (μ : Measure S) (κ : Kernel S S) [IsMarkovKernel κ] :
    @Measure (ℕ → S) MeasurableSpace.pi :=
  MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure κ μ

noncomputable instance MarkovChainPathMeasure.isFiniteMeasure
    (S : Type*) [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ]
    (κ : Kernel S S) [IsMarkovKernel κ] :
    @IsFiniteMeasure (ℕ → S) MeasurableSpace.pi (MarkovChainPathMeasure S μ κ) := by
  unfold MarkovChainPathMeasure
    MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure Kernel.trajMeasure
  infer_instance

/-- **Expectation under the chain started from a point.** For a Markov kernel $\kappa$ on $S$,
a function $Y : S^{\mathbb{N}} \to \mathbb{R}$ of paths and a state $x \in S$, the expectation
$E_x Y$ is the integral of $Y$ against the Markov chain path measure with transition kernel
$\kappa$ and initial distribution the Dirac measure at $x$. -/
noncomputable def markovExpectation
    (S : Type*) [MeasurableSpace S]
    (κ : Kernel S S) [IsMarkovKernel κ] (Y : (ℕ → S) → ℝ) (x : S) : ℝ :=
  ∫ ω, Y ω ∂(MarkovChainPathMeasure S (Measure.dirac x) κ)

/-- **Measurability of the Markov expectation.** Let $S$ be a nonempty standard Borel space,
$\kappa$ a Markov kernel on $S$, and $Y : S^{\mathbb{N}} \to \mathbb{R}$ a bounded function,
measurable for the product $\sigma$-algebra. Then the map $x \mapsto E_x Y$, sending a state
$x$ to the expectation of $Y$ under the Markov chain with transition kernel $\kappa$ started
from $x$, is measurable. -/
theorem measurable_markovExpectation
    (S : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (κ : Kernel S S) [IsMarkovKernel κ]
    (Y : (ℕ → S) → ℝ) (hY_meas : @Measurable _ _ MeasurableSpace.pi _ Y)
    (_hY_bdd : ∃ C : ℝ, ∀ ω, |Y ω| ≤ C) :
    Measurable (markovExpectation S κ Y) := by
  let K := Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0
  let e := MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)
  have hfun : ∀ x : S, markovExpectation S κ Y x = ∫ ω, Y ω ∂(K (e.symm x)) := by
    intro x
    unfold markovExpectation MarkovChainPathMeasure
      MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure Kernel.trajMeasure
    congr 1
    rw [Measure.map_dirac' (MeasurableEquiv.measurable _),
      Measure.dirac_bind (Kernel.measurable _)]
  simp_rw [show markovExpectation S κ Y = fun x => ∫ ω, Y ω ∂(K (e.symm x)) from
    funext hfun]
  exact (hY_meas.stronglyMeasurable.integral_kernel).measurable.comp e.symm.measurable

/-- **Path measure from a point as a trajectory measure.** Let $\kappa$ be a Markov kernel on
$S$, $n \in \mathbb{N}$, and $x = (x_0, \dots, x_n)$ a history of states in $S$. The law on path
space of the Markov chain with transition kernel $\kappa$ and initial distribution the Dirac
measure at $x_n$ equals the Ionescu–Tulcea trajectory measure on $S^{\mathbb{N}}$ started at
time $0$ from the one-entry history $(x_n)$ (the last-coordinate history of $x$), in which each
next state is drawn from $\kappa$ applied to the current state. -/
theorem MarkovChainPathMeasure_dirac_eq_traj {n : ℕ} (x₀ : Π _i : ↥(Finset.Iic n), S) :
    MarkovChainPathMeasure S (Measure.dirac (x₀ ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) κ
      = Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 (lastHist n x₀) := by
  unfold MarkovChainPathMeasure
    MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure Kernel.trajMeasure
  have hsymm : (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm
      (x₀ ⟨n, Finset.mem_Iic.mpr le_rfl⟩) = lastHist n x₀ := by
    funext i
    obtain ⟨ival, hi⟩ := i
    rw [Finset.mem_Iic] at hi
    have : ival = 0 := by omega
    subst this
    rfl
  rw [Measure.map_dirac' (MeasurableEquiv.measurable _), hsymm]
  show (Measure.dirac (lastHist n x₀)).bind (Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0)
      = Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) 0 (lastHist n x₀)
  exact Measure.dirac_bind (Kernel.measurable _) _

/-- **Integral of a shifted path functional.** Let $S$ be a nonempty standard Borel space,
$\kappa$ a Markov kernel on $S$, and $Y : S^{\mathbb{N}} \to \mathbb{R}$ a bounded function,
measurable for the product $\sigma$-algebra. Fix $n \in \mathbb{N}$ and a history
$x = (x_0, \dots, x_n)$ of states in $S$, and let $P_{n,x}$ be the Ionescu–Tulcea trajectory
measure on $S^{\mathbb{N}}$ that equals $x$ at times $0, \dots, n$ and afterwards draws each
next state from $\kappa$ applied to the current state. Then
$$\int Y(\theta_n \omega) \, dP_{n,x}(\omega) = \int Y \, dP_{\delta_{x_n}},$$
where $(\theta_n \omega)_k = \omega_{n+k}$ is the time-$n$ shift and $P_{\delta_{x_n}}$ is the
law on path space of the Markov chain with transition kernel $\kappa$ and initial distribution
the Dirac measure at $x_n$.

The statement also takes a finite measure $\mu$ on $S$, which does not appear in it. -/
theorem integral_shiftPath_traj_eq_markovExpectation
    (S : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (μ : Measure S) [IsFiniteMeasure μ]
    (κ : Kernel S S) [IsMarkovKernel κ]
    (Y : (ℕ → S) → ℝ) (hY_meas : @Measurable _ _ MeasurableSpace.pi _ Y)
    (_hY_bdd : ∃ C : ℝ, ∀ ω, |Y ω| ≤ C)
    (n : ℕ) (x₀ : (_i : ↥(Finset.Iic n)) → S) :
    ∫ ω, Y (shiftPath n ω) ∂(Kernel.traj (X := fun _ : ℕ => S) (markovLiftKernel κ) n x₀) =
      ∫ ω, Y ω ∂(MarkovChainPathMeasure S (Measure.dirac (x₀ ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) κ) := by
  rw [MarkovChainPathMeasure_dirac_eq_traj κ x₀, ← integral_map
    (measurable_shiftPath n).aemeasurable hY_meas.aestronglyMeasurable,
    traj_map_shiftPath_eq κ x₀]

end

end MathlibExt.Probability.MarkovChainPath
