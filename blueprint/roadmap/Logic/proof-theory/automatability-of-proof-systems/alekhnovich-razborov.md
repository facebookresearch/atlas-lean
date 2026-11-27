# Alekhnovich–Razborov: resolution is not automatable unless W[P] is tractable

Call resolution (respectively tree-like resolution) automatable if a deterministic algorithm, given an unsatisfiable CNF $\tau$, returns a resolution (respectively tree-like resolution) refutation of $\tau$ in time polynomial in $|\tau| + S(\tau)$ (respectively $|\tau| + S_T(\tau)$), where $S$ and $S_T$ are the minimum sizes of a resolution and of a tree-like resolution refutation. For a monotone circuit $C$ let $k(C)$ be the minimum Hamming weight of an input satisfying $C$ (the minimum monotone circuit satisfying assignment problem). If resolution or tree-like resolution is automatable, then:

- for every fixed $\varepsilon > 0$ there is an algorithm that, given a monotone circuit $C$, runs in time $\exp(k(C)^{O(1)}) \cdot |C|^{O(1)}$ and approximates $k(C)$ within a factor $1 + \varepsilon$;
- $\mathrm{W}[\mathrm{P}] \subseteq \mathrm{co\text{-}FPR}$, where $\mathrm{FPR}$ is the randomized (one-sided error) analogue of $\mathrm{FPT}$.

In particular, unless $\mathrm{W}[\mathrm{P}]$ is tractable in this randomized sense, neither system is automatable.

## Proof sketch

The core is a polynomial-time map sending a monotone circuit $C$ and an integer $m$ to an unsatisfiable CNF $\tau(C, m)$ with, for $h = \min(k(C), \log m)$,

- a tree-like refutation of size $S_T(\tau(C, m)) \le |C| \cdot m^{O(h)}$, and
- no resolution refutation of size below $S(\tau(C, m)) \ge m^{\Omega(h)}$.

The formula encodes the principle that every $A$-admissible $0$-$1$ matrix with $m$ rows contains a row satisfying $C$, with columns ranging over the columns $A$ of a Paley matrix and each column and control value encoded through a surjective linear code map. Since $S \le S_T$, either automating algorithm runs within $|C|^{O(1)} m^{O(h)}$ and its output size lies between $m^{\Omega(h)}$ and $|C|\, m^{O(h)}$, so it estimates $h$. Choosing $m = 2^{\Theta(\max(k, \log|C|/k))}$ separates $k(C) \le k$ from $k(C) \ge hk$, for an absolute constant $h > 1$, in time $\exp(O(k^2)) |C|^{O(1)}$, and a self-improvement step that composes the circuit with itself turns this constant-gap estimate into the stated approximation and, without the PCP theorem, into the randomized $\mathrm{W}[\mathrm{P}]$ algorithm.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Sources

- M. Alekhnovich, A. A. Razborov, "Resolution is not automatizable unless W[P] is tractable", SIAM Journal on Computing 38 (2008) 1347-1363, doi:10.1137/06066850X (Theorems 2.5 and 2.7, Lemma 3.1); FOCS (2001).
