# Mutation-rate confidence interval from FracMinHash containment

**Simple mutation model.** Let $S$ be a nucleotide sequence with $L$ $k$-mers, all distinct, and let $S'$ be obtained by marking each of the $L+k-1$ positions independently with probability $p \in (0,1)$ and substituting a different nucleotide at every marked position; assume $S'$ also has no repeated $k$-mers and no spurious matches with $S$. Let $A$ and $B$ be the $k$-mer sets of $S$ and $S'$, and $N_{\mathrm{mut}}$ the number of $k$-spans containing at least one mutation, so $|A \setminus B| = N_{\mathrm{mut}}$ and $|A\cap B| = L - N_{\mathrm{mut}}$; each $k$-span is mutated with probability $q = 1 - (1-p)^k$, and $1-p$ is the expected average nucleotide identity. The sketching randomness is independent of the mutation randomness, and $C_{\mathrm{frac}}$ is the [debiased FracMinHash containment](fracminhash-containment-estimator.md) with scale factor $0 < s < 1$, assuming $A \cap B \ne \emptyset$.

**Theorem 5 (mean).** $\ \mathbb{E}[C_{\mathrm{frac}}(A,B)] = (1-p)^k$, so $\hat p = 1 - C_{\mathrm{frac}}(A,B)^{1/k}$ is a point estimate of $p$.

**Theorem 6 (variance).** With $N = N_{\mathrm{mut}}$, to the same first order as the fixed-set variance formula,

$$\operatorname{Var}[C_{\mathrm{frac}}(A,B)] \approx \frac{1-s}{s\,L^3\big(1-(1-s)^L\big)^2}\big(L\,\mathbb{E}[N] - \mathbb{E}[N^2]\big) + \frac{\operatorname{Var}(N)}{L^2},$$

where the moments of $N$ are those under the simple mutation model.

**Theorems 7–8 (test and confidence interval).** Let $\sigma_p^2$ denote the right side of Theorem 6 evaluated at mutation rate $p$, and $z_\alpha = \Phi^{-1}(1-\alpha/2)$. As $L \to \infty$ with $p$, $k$, $s$ fixed, $\Pr\big[(1-p)^k - z_\alpha\sigma_p \le C_{\mathrm{frac}} \le (1-p)^k + z_\alpha\sigma_p\big] \to 1-\alpha$. Inverting, for an observed $C_{\mathrm{frac}}$ and $L$ large enough the equations

$$C_{\mathrm{frac}} = (1-p_{\mathrm{low}})^k + z_\alpha\sigma_{p_{\mathrm{low}}},\qquad C_{\mathrm{frac}} = (1-p_{\mathrm{high}})^k - z_\alpha\sigma_{p_{\mathrm{high}}}$$

have unique solutions, and $\lim_{L\to\infty}\Pr[p_{\mathrm{low}} \le p \le p_{\mathrm{high}}] = 1-\alpha$.

## Expansion

Conditional on the mutation process, $C_{\mathrm{frac}}$ has mean $1 - N/L$, so the tower property and $\mathbb{E}[N] = Lq$ give Theorem 5. The law of total variance splits the variance into the expected sketching variance, obtained by substituting $n = L - N$, $m = N$ in the fixed-set formula (whose numerator $N(L-N)$ has expectation $L\mathbb{E}[N] - \mathbb{E}[N^2]$), plus the variance of $1 - N/L$. Asymptotic normality of $N_{\mathrm{mut}}$ under the mutation model and of $C_{\mathrm{frac}}$ under sketching for fixed $N$ give the two-sided test, and monotonicity of the bounds in $p$ turns it into an interval. Unlike the Poisson model behind Mash, the model accounts for one substitution destroying up to $k$ overlapping $k$-mers. The interval fails when the two sketches share no hash value, which happens with probability $\mathbb{E}[(1-s)^{L-N}]$.

## Depends on

- [Bias correction, variance and asymptotic normality of the FracMinHash containment estimator](fracminhash-containment-estimator.md)

## Sources

- Rahman Hera M, Pierce-Ward NT, Koslicki D, "Deriving confidence intervals for mutation rates across a wide range of evolutionary distances using FracMinHash", Genome Res (2023), Theorems 5–8, Eqs. (5)–(6) and the section "Setting parameters correctly", <https://doi.org/10.1101/gr.277651.123>, PMCID PMC10538494.
