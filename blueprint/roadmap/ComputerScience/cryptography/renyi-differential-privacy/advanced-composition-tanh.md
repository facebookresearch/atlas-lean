# Advanced composition with the $\tanh$ term

Let the adjacency relation be symmetric and let each of $k$ adaptively chosen mechanisms be $(\varepsilon, \delta)$-differentially private, where in round $i$ an adversary, knowing all previous outputs, chooses the mechanism and the pair of adjacent datasets. Then for every $\delta' > 0$ the $k$-fold adaptive composition is

$$
\Bigl(\sqrt{2k\ln(1/\delta')}\,\varepsilon + k\,\varepsilon \tanh(\varepsilon/2),\; k\delta + \delta'\Bigr)\text{-differentially private}.
$$

Since $\tanh(\varepsilon/2) \le e^\varepsilon - 1$, this implies the standard bound with $k\varepsilon(e^\varepsilon - 1)$.

## Proof sketch

Reduce $(\varepsilon, \delta)$ rounds to $(\varepsilon, 0)$ rounds at the cost of $\delta$ each. In an $(\varepsilon, 0)$ round the privacy loss $L = \log(P/Q)$ lies in $[-\varepsilon, \varepsilon]$, and the moment bound shows that its moment generating function under $P$ is at most that of the two-point loss of randomized response, which takes the values $\pm\varepsilon$ and has mean $\varepsilon\tanh(\varepsilon/2)$. By Hoeffding's lemma, $\mathbb{E}_P[e^{sL}] \le \exp(s\varepsilon\tanh(\varepsilon/2) + s^2\varepsilon^2/2)$ for $s \ge 0$. Multiply over the rounds and apply Markov's inequality at the optimal $s$. Kairouz, Oh and Viswanath obtain the same bound from their exact composition theorem, with the slightly smaller $\delta$ part $1 - (1 - \delta)^k(1 - \delta')$, which is at most $k\delta + \delta'$.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Advanced composition](../differential-privacy/differentially-private-pi-advanced.md)

## Proof depends on

- [Rényi-moment bound for bounded privacy loss](privacy-loss-moment-bound.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014, Theorem 3.20 (the bound with $k\varepsilon(e^\varepsilon - 1)$).
- Peter Kairouz, Sewoong Oh and Pramod Viswanath, "The Composition Theorem for Differential Privacy", Proceedings of the 32nd International Conference on Machine Learning (ICML 2015); arXiv:1311.0776v4, Theorem 3.4 (the bound with $(e^\varepsilon - 1)\varepsilon k/(e^\varepsilon + 1) = k\varepsilon\tanh(\varepsilon/2)$).
