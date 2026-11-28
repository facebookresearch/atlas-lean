# Every local randomizer is a mixture of a common component and two clones

Let $R : \mathcal{X} \to \mathcal{Y}$ be an $\varepsilon_0$-differentially private local randomizer and $x^0, x^1 \in \mathcal{X}$. Then there is a randomized algorithm $Q : \{0,1\} \to \mathcal{Y}$ such that

$$
R(x^0) = \frac{e^{\varepsilon_0}}{e^{\varepsilon_0} + 1} Q(0) + \frac{1}{e^{\varepsilon_0} + 1} Q(1), \qquad R(x^1) = \frac{1}{e^{\varepsilon_0} + 1} Q(0) + \frac{e^{\varepsilon_0}}{e^{\varepsilon_0} + 1} Q(1),
$$

as mixtures of distributions. Consequently, for every other input $x$, the output $R(x)$ can be written as a mixture that with probability $e^{-\varepsilon_0}$ is an equal-weight mixture of $Q(0)$ and $Q(1)$ ("a clone" of the differing user) and otherwise is some distribution $\mathrm{LO}(x)$.

## Proof sketch

Let $P_0, P_1$ be the output laws on $x^0, x^1$. The pair $(P_0, P_1)$ is $\varepsilon_0$-indistinguishable, so it is a post-processing of binary randomized response with parameter $\varepsilon_0$ (the extremal $\varepsilon_0$-DP pair); concretely, for $\varepsilon_0 > 0$ solve for $Q(0) = \frac{e^{\varepsilon_0}P_0 - P_1}{e^{\varepsilon_0} - 1}$ and $Q(1) = \frac{e^{\varepsilon_0}P_1 - P_0}{e^{\varepsilon_0} - 1}$, which are probability measures by the privacy inequality. For $\varepsilon_0 = 0$ the privacy inequality forces all output laws of $R$ to coincide, and $Q(0) = Q(1)$ equal to that common law works; the inversion is used only for $\varepsilon_0 > 0$. Since $Q(0) + Q(1) = P_0 + P_1$ in both cases, the equal-weight mixture of $Q(0)$ and $Q(1)$ is $(P_0 + P_1)/2$. For any $x$, $R(x) \ge e^{-\varepsilon_0}\max(P_0, P_1)$ pointwise, hence $R(x) \ge e^{-\varepsilon_0}(P_0 + P_1)/2$, which yields the clone component.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Approximate differential privacy as f-differential privacy](../trade-off-functions-and-gaussian-differential-privacy/epsilon-delta-dp-as-f-dp.md)

## Sources

- V. Feldman, A. McMillan, K. Talwar, "Hiding Among the Clones: A Simple and Nearly Optimal Analysis of Privacy Amplification by Shuffling", FOCS (2021), arXiv:2012.12803, Section 3.
- P. Kairouz, S. Oh, P. Viswanath, "The Composition Theorem for Differential Privacy", ICML (2015); IEEE Transactions on Information Theory 63 (2017), arXiv:1311.0776.
