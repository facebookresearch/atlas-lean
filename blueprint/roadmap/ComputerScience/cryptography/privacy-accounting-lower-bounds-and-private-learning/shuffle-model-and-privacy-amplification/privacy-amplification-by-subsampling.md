# Tight privacy amplification by subsampling

Let $M$ be $(\varepsilon,\delta)$-differentially private. If $M$ is run on a subsample obtained by including each record independently with probability $q$ (Poisson subsampling, neighbouring datasets differing by adding or removing a record), or on a uniformly random subset of fixed size $qn$ (sampling without replacement, neighbouring datasets differing by replacing a record), then the resulting mechanism is

$$
\big(\log(1 + q(e^{\varepsilon} - 1)),\; q\delta\big)\text{-DP}
$$

(with the appropriate pairing of subsampling scheme and neighbouring relation), and this bound is tight: there are mechanisms for which no better $(\varepsilon',\delta')$ pair holds. For small $\varepsilon$ this gives $\varepsilon' \approx q\varepsilon$.

## Proof sketch

Express the subsampled output distribution on each of two neighbouring datasets as a mixture over subsamples, and couple the subsamples so that they coincide except, with probability $q$, in the differing record. Advanced joint convexity of the hockey-stick divergence, $D_{e^{\varepsilon'}}\big((1-q)\mu + q\nu \,\|\, (1-q)\mu + q\nu'\big) = q D_{e^{\varepsilon}}(\nu \| (1-\beta)\mu + \beta\nu')$ with $e^{\varepsilon'} = 1 + q(e^{\varepsilon}-1)$ and $\beta = e^{\varepsilon'}/e^{\varepsilon}$, then reduces to the privacy of $M$ on the coupled pair. Tightness uses randomized response on the subsampled record.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Sources

- B. Balle, G. Barthe, M. Gaboardi, "Privacy Amplification by Subsampling: Tight Analyses via Couplings and Divergences", NeurIPS (2018), arXiv:1807.01647, Theorem 2.
