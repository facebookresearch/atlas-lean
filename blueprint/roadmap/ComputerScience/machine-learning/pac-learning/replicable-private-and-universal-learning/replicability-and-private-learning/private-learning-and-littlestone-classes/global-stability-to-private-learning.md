# Globally stable learners yield private learners via stable histograms

Let $G$ be a randomized learner on $m$ samples such that for every $H$-realizable distribution $D$ some hypothesis $h_D$ with $\mathrm{er}_D(h_D) \le \alpha/2$ satisfies $\Pr_{S \sim D^m}[G(S) = h_D] \ge \eta$. Then $H$ has an $(\varepsilon,\delta)$-differentially private learner that outputs, with probability at least $1-\beta$, a hypothesis of error at most $\alpha$, using

$$
n = O\!\left(\frac{m \log(1/(\eta\beta\delta))}{\eta\, \varepsilon} + \frac{\log(1/(\eta\beta))}{\alpha\, \varepsilon}\right)
$$

samples: run $G$ on $k$ disjoint blocks of $m$ samples, use a private stable-histogram algorithm to release a short list containing every output of frequency at least $\eta$, and choose from the list with the exponential mechanism scored by empirical error on fresh samples.

## Proof sketch

With high probability $h_D$ appears in at least an $\eta/2$ fraction of the $k$ blocks by a Chernoff bound. Changing one example changes the output of at most one block, so the histogram of outputs has sensitivity one per bin; adding Laplace noise to the nonzero bins and thresholding at $O(\log(1/\delta)/\varepsilon)$ is $(\varepsilon,\delta)$-private, since a bin that is nonzero in only one neighbouring dataset has count one and is suppressed except with probability $\delta$. With $k \gtrsim \log(1/(\eta\beta\delta))/(\eta\varepsilon)$ blocks, $h_D$ is on the released list, which has at most $O(1/\eta)$ entries, and the exponential mechanism over the list with $O(\log(1/(\eta\beta))/(\alpha\varepsilon))$ fresh samples returns a hypothesis of error at most $\alpha$.

## Depends on

- [Global stability and list replicability of learning rules](../global-stability-and-list-replicability/global-stability-and-list-replicability.md)
- [Private PAC learners and their sample complexity](private-pac-learner.md)

## Proof depends on

- [The Laplace mechanism is differentially private](../../../../../cryptography/laplace-and-exponential-mechanisms/laplace-mechanism-differentially-private.md)
- [Utility of the exponential mechanism](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism-utility.md)

## Sources

- M. Bun, R. Livni, S. Moran, "An Equivalence Between Private Classification and Online Prediction", FOCS (2020), arXiv:2003.00563, Theorem 17, Lemmas 15 and 16.
