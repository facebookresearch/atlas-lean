# CQR coverage (upper bound without ties)

Under the hypotheses of the [lower bound](of-real-one-sub-le-measure-mem-cqr-band.md) (exchangeable probability law $\mu$ of $n + 1$ data points, measurable $q_{\mathrm{lo}}$, $q_{\mathrm{hi}}$, $0 \le \alpha < 1$, threshold $Q$ with $k = \lceil (1 - \alpha)(n + 1) \rceil$), assume moreover that the $n + 1$ CQR scores $E(Z_1), \dots, E(Z_{n+1})$ are $\mu$-almost surely distinct. Then

$$\mu\big(Y_{n+1} \in C_Q(X_{n+1})\big) \le 1 - \alpha + \frac{1}{n + 1}.$$

## Informally uses

- [Membership in the CQR band through the score](mem-cqr-band-iff.md): coverage of the response is coverage of its score.
- [Upper bound on split conformal coverage without ties](../split-conformal-prediction/measure-coe-le-split-conformal-threshold-2.md): the upper half of the quantile lemma applied to the scores; the source's proof of Theorem 1 gets the term $1 / (|I_2| + 1)$ from the argument of its Lemma 2 (Lemma 1 applied to $n + 1$ scores), although Lemma 2 itself is stated with $1 / n$.

## Sources

- Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*, NeurIPS 2019, arXiv:1905.03222, Theorem 1 (second inequality, $|I_2| = n$ calibration points), conditionally on the proper training set. The source takes $\alpha \in (0, 1)$; the statement above also admits the trivial endpoint $\alpha = 0$.
