# The extended pigeonhole formula needs resolution width at least $n$

For all $n \ge 1$, Duplicator wins the Boolean existential $n$-pebble game on $\mathrm{EPHP}^{n+1}_n$, so every resolution refutation of $\mathrm{EPHP}^{n+1}_n$ has width at least $n$. For every $m > n$ and every row extension, every resolution refutation of $\mathrm{EPHP}^m_n$ has width at least $n/3$.

## Proof sketch

Duplicator maintains a one-to-one partial map from the pigeons into the holes and sets the pigeon and extension variables consistently with it; restrictions of these assignments to at most $n$ variables form a winning strategy, and the pebble-game characterization of width converts this into the width bound $n$. For general $m > n$, Ben-Sasson and Wigderson prove the width bound $n/3$ for every row extension of the pigeonhole formula. (Derived, not stated in this form by the sources: $\mathrm{EPHP}^m_n$ is a $3$-CNF formula, and the space–width inequality $W(\varphi \vdash \bot) \le \mathrm{Sp}(\varphi \vdash \bot) + k - 3$ for $k$-CNF formulas, with $k = 3$, gives clause space at least $n$ for $\mathrm{EPHP}^{n+1}_n$ and at least $n/3$ for $\mathrm{EPHP}^m_n$; Atserias and Dalmau's own inequality $s(F) \ge w(F) - r$ for $r$-CNF formulas gives the weaker clause space bound $n - 3$.)

## Depends on

- [The extended pigeonhole formula $\mathrm{EPHP}^m_n$](extended-pigeonhole-formula.md)
- [The Boolean existential pebble game on a CNF formula](boolean-existential-pebble-game.md)
- [Width of a derivation](../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

- [Clause space of resolution refutations](clause-space-of-resolution.md)
- [Atserias–Dalmau: the existential pebble game characterizes resolution width](atserias-dalmau-width-characterization.md)
- [Atserias–Dalmau inequality: clause space bounds width](clause-space-bounds-width.md)

## Sources

- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", 18th IEEE Conference on Computational Complexity (CCC 2003); journal version Journal of Computer and System Sciences 74(3), 323–334, 2008: Theorem 2, Theorem 3 and Lemma 5 (numbering of the conference version).
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Theorem 4.9.
- Y. Filmus, M. Lauria, M. Mikša, J. Nordström and M. Vinyals, "From Small Space to Small Width in Resolution", 31st Symposium on Theoretical Aspects of Computer Science (STACS 2014), LIPIcs 25, 2014: Theorem 1 (the space–width inequality with $s + k - 3$).
