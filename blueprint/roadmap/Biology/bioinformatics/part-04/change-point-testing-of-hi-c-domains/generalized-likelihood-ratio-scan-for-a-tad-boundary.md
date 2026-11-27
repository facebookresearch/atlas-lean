# Generalized likelihood-ratio scan for a TAD boundary

Let $A = \{(i,j) : 1 \le i \le j \le n\}$ index the upper triangle of a diagonal block of a Hi-C contact matrix with counts $x_{ij}$. A boundary at $m$ ($1 < m < n$) splits $A$ into the two domains $A_{0,1} = \{i \le j \le m\}$, $A_{1,2} = \{m < i \le j\}$ and the inter-domain rectangle $R$. Under the alternative the counts are independent negative binomial with block-constant means,

$$x_{ij} \sim \mathrm{NB}(\mu_k, r), \qquad \mu_k = \mu_1 \text{ on } A_{0,1},\ \mu_2 \text{ on } A_{1,2},\ \mu_0 \text{ on } R,$$

and under the null all means are equal. With block sums $S_{A_1}, S_{A_2}, S_R, S_A$, the generalized likelihood-ratio statistic $\mathrm{GLR}_{\mathrm{NB},m}$ is the difference of the profile NB log-likelihoods of the three-block and one-block fits.

**Theorem 1.** If $m/n$ is held fixed as $n \to \infty$, $\mathrm{GLR}_{\mathrm{NB},m}$ is asymptotically equivalent to the scan statistic $Z_m$, a sum of two squared standardized contrasts: $S_{A_1}$ against its share $\frac{|A_{0,1}|}{|A_{0,1} \cup R|}S_{A_1 \cup R}$ of the pooled sum over $A_{0,1} \cup R$, and $S_{A_1 \cup R}$ against its share $\frac{|A_{0,1}\cup R|}{|A|}S_A$ of the total, each divided by $2\sigma_0^2$ times the corresponding binomial-type variance factor, where $\sigma_0^2$ is the null variance. Since the two contrasts are asymptotically independent, $2Z_m$ is asymptotically $\chi^2_2$, and $Z_m$ detects mean changes without the NB assumption.

**Theorem 2.** Let $\tilde Z = \max_{\xi < m \le n - \xi} Z_m$ with minimal domain size $\xi$. If $m/n \to t \in (0,1)$, then $Z_m \to g_t$, where for a Gaussian random field $G$ on the triangle $B = \{0 \le s \le t' \le 1\}$, with limiting regions $\tilde A_1$ (domain before $t$), $\tilde A_2$ (domain after $t$) and $\tilde R$,

$$g_t = \frac{\big(G_{\tilde A_1} - \frac{t}{2-t}\, G_{\tilde A_1 \cup \tilde R}\big)^2}{2t^2(1-t)/(2-t)} + \frac{\big(G_{\tilde A_1 \cup \tilde R} - t(2-t)\, G_{B}\big)^2}{t(1-t)^2(2-t)};$$

and if $\xi/n \to \delta > 0$, then $\tilde Z \to \max_{\delta < t < 1-\delta} g_t$.

## Depends on

- [Negative binomial mass function with size and mean](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md)
- [Chi-square distribution](../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md)

## Proof depends on

- [Wilks' theorem (simple null)](../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-two-mul-log-like.md)

## Expansion

Under the null the triangle of counts is a random walk with a two-dimensional time index, so Donsker's invariance principle yields the Gaussian-field limit; $|A_{0,1}|/|A_{0,1} \cup R| \to t/(2-t)$ and $|A_{0,1}\cup R|/|A| \to t(2-t)$ give the weights in $g_t$. Critical values are obtained by Monte Carlo from the limit. Boundaries are found top-down by binary segmentation (taking the arg max of $Z_m$ in each sub-block until blocks are smaller than $2\xi$), pruned by re-testing in reverse order, and assigned hierarchy levels bottom-up by re-testing each boundary against its flanking blocks.

## Sources

- H. Xing, Y. Wu, M. Q. Zhang and Y. Chen, "Deciphering hierarchical organization of topologically associated domains through change-point testing", BMC Bioinformatics 22 (2021), Methods, GLR statistic, Theorems 1–2 and Definition 1, <https://doi.org/10.1186/s12859-021-04113-8>, PMCID: PMC8037919.
