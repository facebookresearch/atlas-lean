# Shuffled protocols attain central accuracy for sums but not for selection

In the shuffle model, the sum of $n$ bits can be computed with $(\varepsilon,\delta)$-differential privacy and additive error $O\big(\sqrt{\log(1/\delta)}/\varepsilon\big)$, independent of $n$, by having each user apply randomized response with flip probability of order $\log(1/\delta)/(\varepsilon^2 n)$ and debiasing the shuffled count; local protocols require error $\Omega(\sqrt{n})$, while the central model achieves $O(1/\varepsilon)$. Multi-message shuffled protocols also sum real numbers in $[0,1]$ with error independent of $n$ up to logarithmic factors. In contrast, single-message shuffled protocols for the selection problem (finding an approximately most frequent coordinate among $d$) need exponentially more samples than central-model protocols, so the power of the shuffle model lies strictly between the local and central models.

## Proof sketch

After shuffling, the analyzer sees only the number of ones, which is the true count plus a sum of independent flips; with the stated flip rate the number of flipped bits behaves like a binomial whose variance is $O(\log(1/\delta)/\varepsilon^2)$, and binomial noise of this variance is $(\varepsilon,\delta)$-DP for neighbouring counts. The selection lower bound reduces a restricted shuffled protocol to a local protocol on a smaller population, where known local lower bounds for selection apply.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Local differential privacy is equivalent to statistical query learning](../../../machine-learning/pac-learning/replicable-private-and-universal-learning/replicability-and-private-learning/private-learning-and-littlestone-classes/local-privacy-equals-statistical-queries.md)

## Sources

- A. Cheu, A. Smith, J. Ullman, D. Zeber, M. Zhilyaev, "Distributed Differential Privacy via Shuffling", EUROCRYPT (2019), arXiv:1808.01394.
