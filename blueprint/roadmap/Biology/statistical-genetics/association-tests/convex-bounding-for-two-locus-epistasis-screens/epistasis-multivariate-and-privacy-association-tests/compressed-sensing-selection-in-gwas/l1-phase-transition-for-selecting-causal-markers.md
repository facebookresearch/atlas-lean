# L1 phase transition for selecting causal markers

**Model.** Phenotypes follow the linear model of quantitative genetics

$$y = Ax + e,$$

with $y \in \mathbb R^n$ the phenotypes of $n$ individuals, $A \in \mathbb R^{n \times p}$ the standardized genotype (sensing) matrix over $p$ markers with $p \gg n$, $x \in \mathbb R^p$ the partial regression coefficients with $s$ nonzero entries, and $e$ residual noise of variance $\sigma_E^2$. Recovery is summarized on the phase plane of $\rho = s/n$ (sparsity relative to sample size) against $\delta = n/p$ (undersampling), both in $(0,1)$, with quality measured by the normalized error $\|x - \hat x\|_2 / \|x\|_2$.

**Proposition 1 (noiseless phase transition).** If the entries of $A$ are i.i.d. centered Gaussian (the common variance is immaterial, since rescaling $A$ and $y$ together leaves basis pursuit unchanged) and $e = 0$ (heritability $h^2 = 1$), there is a curve $\rho = \rho_{L_1}(\delta)$ such that, as $n, p, s \to \infty$ with $\rho$ and $\delta$ fixed, basis pursuit

$$\hat x = \arg\min \|\hat x\|_1 \quad \text{subject to } A\hat x = y$$

recovers $\hat x = x$ with probability (over $A$) tending to one below the curve, for every $x$ with $s$ nonzeros, and fails with probability tending to one above it.

**Proposition 2 (noisy recovery).** Let the rows $a_1, \dots, a_n \in \mathbb R^p$ of $A$ be drawn i.i.d. from a distribution $F$ that is isotropic, $E[a a^{\mathsf T}] = I_p$ for $a \sim F$ (unit-variance, uncorrelated markers; for genotypes, markers in linkage equilibrium), with coherence $\gamma$, the smallest number with $\max_t |a_t|^2 \le \gamma$ for $a \sim F$; equivalently, $E[A^{\mathsf T}A] = n I_p$, which is $E[A^{\mathsf T}A] = I_p$ after dividing $A$, $y$ and $e$ by $\sqrt n$, the normalization in which the source states isotropy. Let $e$ have i.i.d. $\mathcal N(0, \sigma_E^2)$ entries independent of $A$, and fix $x$ with $s$ nonzeros and $\beta > 0$. There are a numerical constant $C$ and a constant $C_\beta$ such that, if $n \ge C_\beta\,\gamma\, s \log p$ (and $n \le p$), then with probability at least $1 - 6/p - 6e^{-\beta}$ the lasso

$$\hat x = \arg\min \tfrac12\|y - A\hat x\|_2^2 + \lambda\|\hat x\|_1, \qquad \lambda = 10\,\sigma_E\sqrt{n\log p},$$

(after dividing by $n$, this is the source's penalty $10\sqrt{\log p}\,(\sigma_E/\sqrt n)\,\|\hat x\|_1$ on $\tfrac12\|y/\sqrt n - (A/\sqrt n)\hat x\|_2^2$) satisfies

$$\|\hat x - x\|_2^2 \le C^2(1+\alpha)^2\, \sigma_E^2\, \frac{s \log p}{n}, \qquad \alpha = \sqrt{\frac{(1+\beta)\, s \log^5 p}{n}} \le \log^2 p,$$

that is, $\|\hat x - x\|_2^2 \le \sigma_E^2\,\frac sn\,\mathrm{polylog}(p)$, within a polylogarithmic factor of an oracle that knows the support. The bound is a high-probability statement over the random design and noise, not a deterministic one.

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
- E. J. Candès and Y. Plan, "A probabilistic and RIPless theory of compressed sensing", *IEEE Transactions on Information Theory* 57 (2011), 7235–7254, <https://doi.org/10.1109/TIT.2011.2161794> (preprint arXiv:1011.3854): Section 1 (isotropy and incoherence properties, the normalized model) and Theorem 1.2 (noisy LASSO bound), the source of Proposition 2.
