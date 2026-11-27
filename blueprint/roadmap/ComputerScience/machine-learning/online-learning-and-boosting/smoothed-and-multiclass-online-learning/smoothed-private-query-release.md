# Smoothed analysis of differentially private query release

When the database entries are drawn from $\sigma$-smooth distributions (relative to a base measure $\mu$), there are $(\varepsilon,\delta)$-differentially private algorithms answering the counting queries of a class of VC dimension $d$ (non-adaptive smoothness) or of finite bracketing entropy (adaptive smoothness) with error bounds depending only on $d$ or the bracketing number and polynomially on $\log(1/\sigma)$, in contrast with the worst-case setting, where private learning and query release require finite Littlestone dimension (so that, for example, thresholds and halfspaces over infinite domains are not privately learnable).

## Proof sketch

Private query release reduces to online learning of the dual class through the private multiplicative weights framework, where the regret of the online learner controls the error and the number of costly updates. Under smoothness, the online learner over a finite cover (or bracketing set) of the class has the smoothed regret bounds, which are independent of the Littlestone dimension, and privacy accounting is unchanged.

## Depends on

- [Smoothed adversaries in online learning](smoothed-adversary.md)
- [Differential privacy](../../../cryptography/differential-privacy/differentially-private.md)

## Proof depends on

- [Smoothed regret bounds depending on VC dimension and bracketing numbers](smoothed-online-regret-bounds.md)
- [Private multiplicative weights answers exponentially many counting queries](../../../cryptography/privacy-accounting-lower-bounds-and-private-learning/fingerprinting-lower-bounds-and-adaptive-data-analysis/private-multiplicative-weights.md)
- [Private learning requires log-star of the Littlestone dimension samples](../../pac-learning/replicable-private-and-universal-learning/replicability-and-private-learning/private-learning-and-littlestone-classes/private-learning-requires-log-star-littlestone.md)

## Sources

- N. Haghtalab, T. Roughgarden, A. Shetty, "Smoothed Analysis of Online and Differentially Private Learning", NeurIPS (2020), arXiv:2006.10129.
