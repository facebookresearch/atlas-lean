# Summary-statistic NNLS weights for combining polygenic scores

**Setting.** For a target population $k$, let $P=[\bar\beta^{(1)},\dots,\bar\beta^{(r)}]$ collect $r$ per-SNP polygenic-score weight vectors (for example from several multi-population PRS methods and several source populations), fitted on training summary statistics. With individual-level tuning data $(y,X)$ the ensemble weights are

$$
\hat\omega=\arg\min_{\omega\ge 0}\ \lVert y-XP\omega\rVert_2^2 .
$$

**Statement.** Every quantity needed by the Lawson-Hanson active-set algorithm for this nonnegative least squares problem is a function of tuning summary statistics $\tilde\beta^{\rm tune}$ and the LD matrix $D$, via

$$
(XP)^\top(y-XP\omega)\approx N_{\rm tune}\bigl(P^\top\tilde\beta^{\rm tune}-P^\top DP\,\omega\bigr),\qquad
\bigl((XP_A)^\top XP_A\bigr)^{-1}(XP_A)^\top y\approx(P_A^\top DP_A)^{-1}P_A^\top\tilde\beta^{\rm tune},
$$

for any active set $A$. Running the algorithm with these substitutions (gradient entry, restricted least squares on $A$, step-back to keep $\omega\ge 0$, release of zeroed indices) terminates at the unique minimizer of the summary-statistic quadratic $\omega^\top P^\top DP\,\omega-2\omega^\top P^\top\tilde\beta^{\rm tune}$ over $\omega\ge 0$ when $P^\top DP$ is positive definite. The final score averages the weights over pseudo-GWAS splits, $\omega=\tfrac14\sum_{s=1}^4\omega_s$, and applies them to scores refitted on the full data, $\bar\beta^{\rm ens}=P\omega$.

## Expansion

The least squares objective depends on the data only through $X^\top X/N_{\rm tune}\approx D$ and $X^\top y/N_{\rm tune}=\tilde\beta^{\rm tune}$, so the Karush-Kuhn-Tucker conditions of NNLS and every step of the active-set method translate verbatim into summary-statistic form. Nonnegativity keeps the ensemble interpretable and acts as regularization against overfitting to correlated component scores. Because the tuning half must be independent of the training half, the weights are only trustworthy when combined with an independence-preserving split such as Gaussian data fission on LD-pruned SNPs, where $D\approx I$.

## Depends on

- [Gaussian data fission of GWAS summary statistics](gaussian-data-fission-of-gwas-summary-statistics.md)

## Sources

- Xu L, Dong Y, Zeng X, Bian Z, Zhou G, Guan L, Zhao H. MIXPRS enables multi-population and multi-method polygenic risk scores using summary statistics. *Nature Genetics* (2026). <https://doi.org/10.1038/s41588-026-02637-4>. PMCID: PMC13364660. Methods, Steps 2-3, Algorithm 1.
- Lawson CL, Hanson RJ. *Solving Least Squares Problems*. SIAM (1995).
