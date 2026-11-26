# Measure-and-reprogram for quantum random oracles

Let $\mathcal{A}$ be a $q$-query quantum algorithm with access to a random oracle $H:X\to Y$ that outputs $(x,z)$, and let $V(x,H(x),z)$ be a predicate. There is a simulator $\mathcal{S}$ that runs $\mathcal{A}$, measures one of its $q+1$ query or output registers (chosen at random) to obtain $x$, provides a fresh uniformly random value $\Theta$ as $H(x)$ for the remainder (reprogramming), and outputs $(x,z)$, such that for every $x_0$ and every predicate,

$$
\Pr_{\Theta}\bigl[\mathcal{S}\text{ outputs }(x_0,z)\text{ with }V(x_0,\Theta,z)\bigr]\ge\frac{1}{(2q+1)^{2}}\Pr_H\bigl[\mathcal{A}^{H}\text{ outputs }(x_0,z)\text{ with }V(x_0,H(x_0),z)\bigr].
$$

For multi-round protocols with $k$ reprogramming points the loss is $O(q^{2k})$-type, which yields Fiat–Shamir security in the QROM.

## Proof sketch

Write the adversary's final state as a sum over the query index $i$ at which $x_0$ is first "fixed". Measuring a random query and reprogramming there produces a state whose overlap with the successful component is at least $1/(2q+1)$ in amplitude, by an orthogonal decomposition of the state into components that do and do not depend on $H(x_0)$ before and after each query. Squaring gives the bound.

## Depends on

- [The quantum random oracle model](quantum-random-oracle-model.md)
- [One-way to hiding lemma for reprogramming quantum random oracles](one-way-to-hiding.md)

## Proof depends on

- [The quantum random oracle model](quantum-random-oracle-model.md)

## Sources

- Jelle Don, Serge Fehr, Christian Majenz, Christian Schaffner, "Security of the Fiat-Shamir Transformation in the Quantum Random-Oracle Model", CRYPTO (2019), arXiv:1902.07556.
