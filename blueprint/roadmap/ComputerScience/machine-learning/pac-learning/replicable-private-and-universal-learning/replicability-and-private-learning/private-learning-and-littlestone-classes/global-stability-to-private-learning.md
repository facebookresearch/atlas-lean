# Globally stable learners yield private learners via stable histograms

Let $H$ have an $\eta$-globally stable learner $G$ on $m$ samples whose frequently output hypothesis $h_D$ has error at most $\alpha$. Then $H$ has an $(\varepsilon,\delta)$-differentially private $(\alpha, \beta)$-accurate learner using

$$
n = O\!\left(\frac{m \log(1/(\eta\beta\delta))}{\eta\, \varepsilon}\right)
$$

samples: split the sample into $k = n/m$ blocks, run $G$ on each, and release the most frequent output by a stable-histogram (private mode selection) mechanism, outputting nothing if no output is frequent enough.

## Proof sketch

With high probability $h_D$ appears in at least an $\eta/2$ fraction of the $k$ blocks by a Chernoff bound. Changing one example changes the output of at most one block, so the histogram of outputs has sensitivity one per bin; adding Laplace noise to the nonzero bins and thresholding at $O(\log(1/\delta)/\varepsilon)$ is $(\varepsilon,\delta)$-private, since a bin that is nonzero in only one neighbouring dataset has count one and is suppressed except with probability $\delta$. With $k \gtrsim \log(1/(\eta\beta\delta))/(\eta\varepsilon)$ blocks, $h_D$ survives the threshold and is the noisy maximum.

## Depends on

- [Global stability and list replicability of learning rules](../global-stability-and-list-replicability/global-stability-and-list-replicability.md)
- [Private PAC learners and their sample complexity](private-pac-learner.md)

## Proof depends on

- [The Laplace mechanism is differentially private](../../../../../cryptography/laplace-and-exponential-mechanisms/laplace-mechanism-differentially-private.md)

## Sources

- M. Bun, R. Livni, S. Moran, "An Equivalence Between Private Classification and Online Prediction", FOCS (2020), arXiv:2003.00563.
