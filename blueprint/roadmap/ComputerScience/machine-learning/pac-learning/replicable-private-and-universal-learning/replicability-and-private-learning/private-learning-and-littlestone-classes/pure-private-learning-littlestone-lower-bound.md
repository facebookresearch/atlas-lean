# Pure private learning needs at least the Littlestone dimension many samples

For every class $H$, the sample complexity of pure ($\delta = 0$) $\varepsilon$-differentially private PAC learning with constant accuracy satisfies $\mathrm{SC}_{\varepsilon,0}(H) = \Omega(\mathrm{Ldim}(H)/\varepsilon)$, and at constant accuracy and confidence $\mathrm{SC}_{\varepsilon,0}(H) = \Theta\big(R^{\to,\mathrm{pub}}(H)/\varepsilon\big)$, where $R^{\to,\mathrm{pub}}(H)$ is the public-coin randomized one-way communication complexity of the evaluation problem $(h, x) \mapsto h(x)$ for $h \in H$ held by Alice and $x \in X$ held by Bob (the shared random string corresponds to the random choice of hypothesis set in a probabilistic representation; private-coin protocols correspond instead to deterministic representations). In particular, for a fixed privacy parameter, such as $\varepsilon = 1$, the pure private sample complexity equals this public-coin communication complexity up to constant factors. Consequently, for every $t$ there is a class with Littlestone dimension $2$ whose pure private sample complexity is at least $t$, and there are classes (lines in $\mathbb{Z}_p^2$) for which, at constant accuracy, pure $\varepsilon$-private learning needs $\Omega(t/\varepsilon)$ samples while $(\varepsilon, \delta)$-private learning needs only $O(\log(1/\delta)/\varepsilon)$.

## Proof sketch

A pure private learner is a distribution over hypotheses with the property that every target has a large-probability good hypothesis; by the exponential-mechanism characterization (probabilistic representation dimension of Beimel, Nissim and Stemmer), its sample complexity equals the logarithm of the size of such a randomized representation, which is a one-way public-coin protocol for evaluation. One-way communication of evaluation is bounded below by the Littlestone dimension by embedding the augmented index problem along a Littlestone tree.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Utility of the exponential mechanism](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism-utility.md)

## Sources

- V. Feldman, D. Xiao, "Sample Complexity Bounds on Differentially Private Learning via Communication Complexity", COLT (2014); SIAM Journal on Computing 44 (2015), arXiv:1402.6278, Definitions 2.3 and 2.4, Theorems 1.1–1.3, 2.5 and Corollary 4.3.
- A. Beimel, K. Nissim, U. Stemmer, "Characterizing the Sample Complexity of Private Learners", ITCS (2013), arXiv:1402.2224.
