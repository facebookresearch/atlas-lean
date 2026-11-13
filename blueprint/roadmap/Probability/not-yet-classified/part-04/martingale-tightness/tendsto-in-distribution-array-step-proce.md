# Functional CLT for martingale difference arrays in `D((0,1))`

**Functional CLT for martingale difference arrays in `D([0,1])`** (McLeish's invariance
principle with tightness from Aldous's criterion).

Let row `n` of `ξ` be a square-integrable martingale difference sequence for the filtration
`𝓕 n`, with
* predictable quadratic variation converging to the identity: for every `t ∈ [0,1]`,
  `∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j] → t` in probability;
* the Lindeberg condition `LindebergConditionTriangular ξ μ`;
* (**T81, taken as a hypothesis**) finite-dimensional convergence of the step process to a
  continuous process `Z`: for every finite set of times `I ⊆ [0,1]`,
  `(∑_{i < ⌊n t⌋} ξ n i)_{t ∈ I} → (Z t)_{t ∈ I}` in distribution. This is the conclusion of
  McLeish's martingale CLT (roadmap task T81: quadratic-variation convergence + Lindeberg ⇒
  finite-dimensional convergence to Brownian motion), which is not yet in the library; `Z` is
  meant to be Brownian motion on `[0,1]`.

Then the step processes `arrayStepProcess n ξ` converge in distribution to `Z` in the Skorokhod
J1 topology on `D([0,1])`.

Proof: T43's transfer theorem `tendstoInDistribution_skorokhod_of_tight_of_fdd` applied to the
step processes and their polygonal interpolations `arrayPolygon n ξ`. Tightness of the polygons
is Aldous's criterion (`isTightMeasureSet_arrayPolygon_of_aldousCondition`), whose condition
comes from the martingale structure and quadratic-variation convergence
(`aldousCondition_of_martingaleDifference`); the jumps vanish by Lindeberg
(`tendsto_measure_exists_abs_gt_of_lindeberg`), which also transfers the finite-dimensional
convergence from the step process to the polygon (Slutsky).

## Sources

- McLeish (1974), §3; Jacod–Shiryaev (2003), Theorems VI.4.5 and VI.4.13 and §VIII.3; Billingsley (1999), §18.
