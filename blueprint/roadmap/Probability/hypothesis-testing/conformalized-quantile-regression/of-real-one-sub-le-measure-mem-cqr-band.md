# CQR coverage (lower bound)

Let $\mathcal{X}$ be a measurable space, $n \in \mathbb{N}$, and let the law $\mu$ of the data $Z = (Z_1, \dots, Z_{n+1}) \in (\mathcal{X} \times \mathbb{R})^{n+1}$ ($n$ calibration points, then the test point $Z_{n+1} = (X_{n+1}, Y_{n+1})$) be a probability measure invariant under every permutation of the coordinates. Let $q_{\mathrm{lo}}, q_{\mathrm{hi}} : \mathcal{X} \to \mathbb{R}$ be measurable and $0 \le \alpha < 1$, and let $Q$ be the [CQR threshold](cqr-threshold.md) with $k = \lceil (1 - \alpha)(n + 1) \rceil$. Then

$$\mu\big(Y_{n+1} \in C_Q(X_{n+1})\big) \ge 1 - \alpha,$$

where $C_Q$ is the [CQR band](cqr-band.md).

The proof is the one in the source: the response lies in the band iff its score is at most the threshold, and the scores of exchangeable data computed with fixed $q_{\mathrm{lo}}$, $q_{\mathrm{hi}}$ are exchangeable, so split conformal coverage applies to the score vector.

## Informally uses

- [Membership in the CQR band through the score](mem-cqr-band-iff.md): coverage of the response is coverage of its score.
- [Split conformal coverage](../split-conformal-prediction/of-real-one-sub-le-measure-coe-le-split.md): the lower bound of the quantile lemma (Lemma 2 of the source) applied to the exchangeable scores.

## Sources

- Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*, NeurIPS 2019, arXiv:1905.03222, Theorem 1 (first inequality), stated conditionally on the proper training set (fixed $q_{\mathrm{lo}}$, $q_{\mathrm{hi}}$), as in its proof. The source takes $\alpha \in (0, 1)$; the statement above also admits the trivial endpoint $\alpha = 0$.
