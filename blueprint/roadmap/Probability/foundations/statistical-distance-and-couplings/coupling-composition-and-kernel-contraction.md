# Sequential composition of couplings and contraction of a common kernel

Let $\mu, \nu$ be discrete distributions on $\alpha$ and $f, g$ Markov kernels from $\alpha$ to $\beta$.

1. If $\mu, \nu$ are coupled within $\varepsilon$ and $f(a), g(a)$ are coupled within $\eta$ for every $a$ in the support of $\nu$, then the mixtures $\mu f$ and $\nu g$ are coupled within $\varepsilon + \eta$. Independent couplings combined by a map $(a, b) \mapsto h(a, b)$ add their disagreement bounds.
2. On finite sets, if $D = \max_{a, a'}\delta(K(a), K(a'))$ bounds the distance between rows of a Markov kernel $K$, then $\delta(\mu K, \nu K) \le D\, \delta(\mu, \nu)$.

## Proof sketch

Item 1 follows from the event characterization of approximate couplings: for every event $S$, $\mu f(S) \le \nu f(S) + \varepsilon$ and $\nu f(S) \le \nu g(S) + \eta$. For item 2, take an optimal coupling $\omega$ of $\mu, \nu$ and write $\mu K - \nu K = \sum_{a \ne a'} \omega(a,a')(K(a) - K(a'))$; each row difference has half-$\ell_1$ norm at most $D$ and the total off-diagonal mass is $\delta(\mu,\nu)$.

## Depends on

- [Approximate coupling of discrete distributions](approximate-coupling.md)

## Proof depends on

- [Maximal couplings realize statistical distance](maximal-coupling-theorem.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017.
