# Parity systems and bounded-width derivations

A *parity system* is a finite list of equations $\bigoplus_{i \in S} x_i = b$ over $\mathbb{F}_2$, each given by a set $S$ of variables and $b \in \{0,1\}$. A *width-$d$ derivation* from a parity system adds (XORs) two derived equations whenever the sum has at most $d$ variables; the system is *refuted in width $d$* if $0 = 1$ (the empty sum with right-hand side $1$) is derivable. Over $\pm 1$ variables the equation reads $\prod_{i \in S} x_i = (-1)^b$, giving the $\pm1$ polynomial encoding with axioms $x_i^2 = 1$.

## Sources

- D. Grigoriev, "Linear Lower Bound on Degrees of Positivstellensatz Calculus Proofs for the Parity", Theoretical Computer Science 259(1–2), 613–622, 2001.
- G. Schoenebeck, "Linear Level Lasserre Lower Bounds for Certain k-CSPs", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008: Definition 10 (width-$w$ resolution on XOR formulas).
