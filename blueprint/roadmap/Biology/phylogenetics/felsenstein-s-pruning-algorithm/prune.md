# Felsenstein's pruning recursion

For a commutative semiring $R$, a finite state set $S$ and leaf weights $\mathrm{obs}$, the partial likelihood of a [tree](tree.md) given the state $s$ at its root is defined recursively:

- for a leaf $l$: $\mathrm{pr}(l, s) = \mathrm{obs}(l, s)$;
- for an internal node with weights $P, Q$ and children $l, r$:

$$\mathrm{pr}(t, s) = \Bigl(\sum_{a \in S} P(s, a)\, \mathrm{pr}(l, a)\Bigr) \Bigl(\sum_{b \in S} Q(s, b)\, \mathrm{pr}(r, b)\Bigr).$$
