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

/-- Compatibility name for the canonical lifted transition kernel. -/
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

/-- One-step shift for `partialTraj` (measure form). -/
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

/-- The last-coordinate history of `x₀`. -/
def lastHist (a : ℕ) (x₀ : Π _i : ↥(Finset.Iic a), S) : Π _i : ↥(Finset.Iic 0), S :=
  fun _i => x₀ ⟨a, Finset.mem_Iic.mpr le_rfl⟩

lemma measurable_lastHist (a : ℕ) : Measurable (lastHist (S := S) a) := by
  apply Measurable.of_eval; intro i
  exact measurable_pi_apply (⟨a, Finset.mem_Iic.mpr le_rfl⟩ : ↥(Finset.Iic a))

/-- Kernel form of the one-step shift. -/
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

/-- Finite-dimensional distributions of the shifted trajectory depend only on the
last coordinate of the initial history. -/
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

/-- The shift on path space. -/
def shiftPath (n : ℕ) : (ℕ → S) → (ℕ → S) :=
  fun ω k => ω (n + k)

lemma measurable_shiftPath (n : ℕ) : Measurable (shiftPath (S := S) n) := by
  apply Measurable.of_eval; intro k
  exact measurable_pi_apply (n + k)

omit [MeasurableSpace S] in
/-- Finite restrictions of the shifted trajectory. -/
lemma frestrictLe_comp_shiftPath (n b : ℕ) :
    (Preorder.frestrictLe (π := fun _ : ℕ => S) b) ∘ (shiftPath (S := S) n)
      = (dropHist n b) ∘ (Preorder.frestrictLe (π := fun _ : ℕ => S) (n + b)) := by
  funext ω i
  rfl

/-- The law of the shifted trajectory depends only on the last coordinate. -/
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


/-- The canonical filtration on the path space `ℕ → S`: at time `n` it is the
σ-algebra generated by the coordinate maps `ω ↦ ω i` for `i ≤ n`. -/
noncomputable def pathFiltration (S : Type*) [MeasurableSpace S] :
    Filtration ℕ
      (m := MeasurableSpace.pi (m := fun _ : ℕ => (inferInstance : MeasurableSpace S))) where
  seq n := ⨆ (i : ℕ) (_ : i ≤ n),
    MeasurableSpace.comap (fun (ω : ℕ → S) => ω i) ‹MeasurableSpace S›
  mono' i j hij := iSup_mono fun k => iSup_mono' fun hk => ⟨hk.trans hij, le_rfl⟩
  le' n := iSup_le fun k => iSup_le fun _ => (measurable_pi_apply k).comap_le

/-- Each level of the `pathFiltration` is contained in the product σ-algebra on `ℕ → S`. -/
lemma pathFiltration_le_pi (S : Type*) [MeasurableSpace S] (n : ℕ) :
    pathFiltration S n ≤ MeasurableSpace.pi := by
  exact (pathFiltration S).le' n

/-- The law on path space of the Markov chain with initial distribution `μ` and
transition kernel `κ`. -/
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

/-- The expectation `E_x Y` of a path functional `Y` under the chain started from `x`. -/
noncomputable def markovExpectation
    (S : Type*) [MeasurableSpace S]
    (κ : Kernel S S) [IsMarkovKernel κ] (Y : (ℕ → S) → ℝ) (x : S) : ℝ :=
  ∫ ω, Y ω ∂(MarkovChainPathMeasure S (Measure.dirac x) κ)

/-- The map `x ↦ E_x Y` is measurable. -/
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

/-- The path measure with Dirac initial law is the trajectory kernel at the
singleton history. -/
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

/-- **Integral of a shifted path functional.** The integral of `Y` composed with
the time-`n` shift against the trajectory measure started from a history `x₀`
equals the integral of `Y` against the path measure started from the last
coordinate of `x₀`. -/
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
