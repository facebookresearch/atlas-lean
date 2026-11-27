# Max-statistic permutation p-value for copy-number aberration units

Let $X = (x_{nm})$ be an $N \times M$ matrix of log copy-number ratios ($N$ tumours, $M$ ordered probes), thresholded so that only amplified entries ($x_{nm} \ge \theta_{\mathrm{amp}}$) are kept. Consecutive aberrant probes are merged into regions and cut wherever the across-sample Pearson correlation of adjacent probes falls below a threshold $\theta_\rho$; the resulting runs $u(k,L)$ (start probe $k$, length $L$) are *CNA units*. The unit score is

$$U_{k,L}(X) = \frac{1}{LN}\sum_{n=1}^N \sum_{l=k}^{k+L-1} x_{nl}.$$

Let $X^{(1)},\dots,X^{(T)}$ be random within-sample positional permutations that relocate the already-defined units of each sample along the genome (never across samples). For an observed unit of length $L$ define

$$P\bigl(U_{k,L}(X)\bigr) = \frac{1 + \sum_{t=1}^T \mathbb{1}\Bigl[\max_{k'} U_{k',L}(X^{(t)}) \ge U_{k,L}(X)\Bigr]}{T+1},$$

where the maximum runs over all windows of $L$ consecutive probes. If, under the null hypothesis that no aberration is recurrent, the observed matrix and the $T$ permuted matrices are exchangeable, then for every $u \in [0,1]$ the probability that some length-$L$ unit gets $P \le u$ is at most $u$: the p-values are valid and control the family-wise error rate over all units of that length. Deletions are treated in the same way with left tails.

## Proof depends on

- [Validity of the Fisher randomization test](../../../Probability/not-yet-classified/part-06/fisher-randomization/is-valid-pvalue-fisher-randomization.md)

## Expansion

Comparing every unit with the maximum score over the whole permuted genome is the max-$T$ device: a family-wise error occurs only if the observed maximum ranks among the top $\lfloor u(T+1)\rfloor$ of $T+1$ exchangeable maxima, which has probability at most $u$; the $+1$ in numerator and denominator makes the Monte Carlo p-value exact rather than anti-conservative. Permuting whole units preserves the correlation between adjacent probes that per-probe permutation, as in the [GISTIC permutation null](../gistic-permutation-null-for-copy-number-scores/permutation-null.md), destroys, and computing the null separately for each length $L$ accounts for the length dependence of background aberration rates.

## Sources

- X. Yuan, G. Yu, X. Hou, I.-M. Shih, R. Clarke, J. Zhang, E. P. Hoffman, R. R. Wang, Z. Zhang and Y. Wang, "Genome-wide identification of significant aberrations in cancer genome", BMC Genomics 13 (2012), 342, <https://doi.org/10.1186/1471-2164-13-342>, PMCID PMC3428679. Definitions 1 and 2, Eqs. (1)–(4) and Algorithm 1.
