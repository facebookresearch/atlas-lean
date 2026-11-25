# Regret of Exp3 for adversarial bandits

Consider a $k$-armed oblivious adversarial bandit with $k \ge 2$ with reward table $x \in [0,1]^{n \times k}$. Exp3 runs
exponential weights with learning rate $\eta$ on the importance-weighted loss estimates
$\hat{Y}_{tj} = \mathbb{1}[A_t = j](1 - x_{tj})/P_{tj}$, where $P_{tj}$ is the probability of choosing arm
$j$ at round $t$. With $\eta = \sqrt{\log(k)/(nk)}$ its regret satisfies $R_n \le 2\sqrt{nk \log k}$, and
with $\eta = \sqrt{2\log(k)/(nk)}$ it satisfies $R_n \le \sqrt{2 nk \log k}$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: unbiasedness of the importance-weighted loss estimator when every arm is chosen with positive probability.
- Proof prerequisite: the second-order exponential-weights bound with coefficient $\eta/2$ on the second moment, from $e^x \le 1 + x + x^2/2$ for $x \le 0$, which gives the constant in $\sqrt{2nk\log k}$.

## Depends on

- [Oblivious adversarial bandits](oblivious-adversarial-bandits.md)

## Proof depends on

- [The second-order Hedge bound](../../online-learning-and-boosting/hedge-algorithm/alg-loss-le-sq.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Algorithm 9, Theorems 11.1 and 11.2. <https://tor-lattimore.com/downloads/book/book.pdf>
