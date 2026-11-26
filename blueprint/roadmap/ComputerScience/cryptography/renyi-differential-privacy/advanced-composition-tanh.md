# Advanced composition with the $\tanh$ term

Let the adjacency relation be symmetric and let each of $k$ adaptively chosen mechanisms be $(\varepsilon, \delta)$-differentially private, where in round $i$ an adversary, knowing all previous outputs, chooses the mechanism and the pair of adjacent datasets. Then for every $\delta' > 0$ the $k$-fold adaptive composition is

$$
\Bigl(\sqrt{2k\ln(1/\delta')}\,\varepsilon + k\,\varepsilon \tanh(\varepsilon/2),\; k\delta + \delta'\Bigr)\text{-differentially private}.
$$

Since $\tanh(\varepsilon/2) \le e^\varepsilon - 1$, this implies the standard bound with $k\varepsilon(e^\varepsilon - 1)$.

## Proof sketch

Reduce $(\varepsilon, \delta)$ rounds to $(\varepsilon, 0)$ rounds at the cost of $\delta$ each, bound the moment generating function of the total privacy loss by the product of the per-round Rényi-moment bounds, and apply Markov's inequality at the optimal order.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Advanced composition](../differential-privacy/differentially-private-pi-advanced.md)

## Proof depends on

- [Rényi-moment bound for bounded privacy loss](privacy-loss-moment-bound.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
