# L1 phase transition for selecting causal markers

**Model.** Phenotypes follow the linear model of quantitative genetics

$$y = Ax + e,$$

with $y \in \mathbb R^n$ the phenotypes of $n$ individuals, $A \in \mathbb R^{n \times p}$ the standardized genotype (sensing) matrix over $p$ markers with $p \gg n$, $x \in \mathbb R^p$ the partial regression coefficients with $s$ nonzero entries, and $e$ residual noise of variance $\sigma_E^2$. Recovery is summarized on the phase plane of $\rho = s/n$ (sparsity relative to sample size) against $\delta = n/p$ (undersampling), both in $(0,1)$, with quality measured by the normalized error $\|x - \hat x\|_2 / \|x\|_2$.

**Proposition 1 (noiseless phase transition).** If $A$ has i.i.d. Gaussian entries and $e = 0$ (heritability $h^2 = 1$), there is a curve $\rho = \rho_{L_1}(\delta)$ such that, as $n, p, s \to \infty$ with $\rho$ and $\delta$ fixed, basis pursuit

$$\hat x = \arg\min \|\hat x\|_1 \quad \text{subject to } A\hat x = y$$

recovers $\hat x = x$ with probability tending to one below the curve and fails with probability tending to one above it.

**Proposition 2 (noisy recovery).** Call $A$ isotropic if $E[A^{\mathsf T}A] = I$ (for genotypes, markers in linkage equilibrium), and let its coherence be the smallest $\gamma$ with $\max_t |a_t|^2 \le \gamma$ for every row $a$. If $A$ is isotropic with coherence $\gamma$ and $n > C\gamma s \log p$ for a constant $C$, the lasso

$$\hat x = \arg\min \|y - A\hat x\|_2^2 + \lambda\|\hat x\|_1$$

with suitable $\lambda$ satisfies $\|\hat x - x\|_2^2 \le \sigma_E^2\, \frac sn\, \mathrm{polylog}(p)$, within a polylogarithmic factor of an oracle that knows the support.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

- [Exact recovery by basis pursuit](../../../../../../Probability/linear-models-multivariate/exact-recovery-by-basis-pursuit/basis-pursuit-unique-iff-restricted-null.md)

## Expansion

Although $Ax = y$ has infinitely many solutions when $n < p$, the $L_1$ ball's low-dimensional faces make the sparsest consistent vector the unique minimizer for most sensing matrices once $n$ is large relative to $s$, which is the content of the Donoho–Tanner curve. In the noisy case the threshold scales linearly in $s$ and only logarithmically in $p$, so adding markers barely raises the required sample size, and support recovery can be complete before coefficient magnitudes are well estimated. The location of the transition also supplies a data-internal diagnostic: as $n$ grows on a fixed dataset, a sudden drop in the size and instability of the selected set signals that the favourable phase has been reached.

## Simulation results

**Empirical boundary.** On real genotype matrices the same sharp transition appears at $h^2 = 1$; for $h^2 \approx 0.5$ the transition is smoothed but complete selection of the nonzeros occurs once $n \approx 30\,s$, a threshold depending only weakly on $p$ and robust to linkage disequilibrium between causal variants and nearby markers.

## Sources

- S. Vattikuti, J. J. Lee, C. C. Chang, S. D. H. Hsu, C. C. Chow, "Applying compressed sensing to genome-wide association studies", GigaScience 3:10 (2014), Eq 1, Propositions 1–2, Definitions 1–2 and the phase-plane results, <https://doi.org/10.1186/2047-217x-3-10>, PMCID PMC4078394.
