# Binary randomized response: privacy and variance of the debiased sum

Binary randomized response with parameter $\varepsilon_0 \ge 0$ reports its input bit $x \in \{0,1\}$ with probability $e^{\varepsilon_0}/(e^{\varepsilon_0} + 1)$ and the flipped bit otherwise; it is an $\varepsilon_0$-differentially private local randomizer, and it is extremal: every $\varepsilon_0$-local randomizer restricted to two inputs is a post-processing of it. For $\varepsilon_0 > 0$, the debiased estimate $\hat x = \big((e^{\varepsilon_0}+1)y - 1\big)/(e^{\varepsilon_0} - 1)$ of a report $y$ is unbiased with variance $e^{\varepsilon_0}/(e^{\varepsilon_0} - 1)^2$, so the local-model estimate of a sum of $n$ bits has standard deviation $\sqrt{n e^{\varepsilon_0}}/(e^{\varepsilon_0} - 1) = \Theta(\sqrt{n}/\varepsilon_0)$ for $\varepsilon_0 \le 1$, in contrast with error $O(1/\varepsilon)$ in the central model.

## Proof sketch

The ratio of report probabilities under inputs $0$ and $1$ is $e^{\pm\varepsilon_0}$, which is $\varepsilon_0$-DP. With $q = e^{\varepsilon_0}/(e^{\varepsilon_0}+1)$, $\mathbb{E}[y] = (1-q) + x(2q - 1)$, so for $\varepsilon_0 > 0$ (where $2q - 1 > 0$) $\hat x = (y - (1-q))/(2q-1)$ is unbiased, and $\mathrm{Var}(\hat x) = q(1-q)/(2q-1)^2 = e^{\varepsilon_0}/(e^{\varepsilon_0}-1)^2$. At $\varepsilon_0 = 0$ the report is an input-independent fair coin, so no estimator is unbiased for both inputs. Extremality is the mixture decomposition into two clones.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Every local randomizer is a mixture of a common component and two clones](local-randomizer-mixture-decomposition.md)

## Sources

- P. Kairouz, S. Oh, P. Viswanath, "The Composition Theorem for Differential Privacy", ICML (2015); IEEE Transactions on Information Theory 63 (2017), arXiv:1311.0776.
- A. Cheu, A. Smith, J. Ullman, D. Zeber, M. Zhilyaev, "Distributed Differential Privacy via Shuffling", EUROCRYPT (2019), arXiv:1808.01394.
