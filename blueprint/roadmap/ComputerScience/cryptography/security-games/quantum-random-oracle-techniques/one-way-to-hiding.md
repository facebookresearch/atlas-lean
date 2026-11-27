# One-way to hiding lemma for reprogramming quantum random oracles

Let $G,H$ be oracles that differ only on a set $S$, and let $\mathcal{A}$ make at most $q$ queries (of depth at most $d$). Let $\mathcal{B}$ run $\mathcal{A}$ with oracle $H$ and, at a uniformly random query, measure the query input register, outputting the result $x$. Then for any input $z$,

$$
\bigl|\Pr[\mathcal{A}^{H}(z)=1]-\Pr[\mathcal{A}^{G}(z)=1]\bigr|\le 2q\sqrt{\Pr[\mathcal{B}^{H}(z)\in S]},
$$

and in the semi-classical refinement the factor $2q$ improves to $2\sqrt{(d+1)\Pr[\text{find}]}$, where "find" is the event that a semi-classical oracle measuring membership in $S$ returns true. This lemma allows reprogramming of quantum random oracles at points the adversary is unlikely to query.

## Proof sketch

Hybrid over queries: the difference between running with $H$ and with $G$ is a sum of $q$ terms, each bounded by twice the norm of the query state's projection onto $S$. Cauchy–Schwarz turns the sum of norms into $\sqrt{q\sum_i\|\Pi_S\psi_i\|^{2}}=q\sqrt{\Pr[\mathcal{B}\in S]}$. The semi-classical version tracks the event of a measured hit and uses depth instead of query count.

## Depends on

- [The quantum random oracle model](quantum-random-oracle-model.md)

## Sources

- Andris Ambainis, Mike Hamburg, Dominique Unruh, "Quantum Security Proofs Using Semi-classical Oracles", CRYPTO (2019).
