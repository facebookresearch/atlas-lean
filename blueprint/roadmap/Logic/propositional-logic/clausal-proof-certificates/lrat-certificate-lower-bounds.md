# Exponential lower bounds for LRAT certificates

Every LRAT certificate (without extension or RAT steps) accepted for $\mathrm{PHP}^{n+1}_n$ satisfies $2^{n/24} \le (n+1) + n(n+1)^2 + \min(H, S \cdot n(n+1))$, so its number of hints, and hence its length, is $2^{\Omega(n)}$. Likewise there is a family of unsatisfiable $O(1)$-CNF formulas with $O(n)$ variables and clauses (Tseitin formulas on expanders) all of whose accepted certificates have length $2^{\Omega(n)}$. These bound the certificate, regardless of the solver that produced it.

## Proof sketch

Translate an accepted certificate into a resolution refutation of size at most $|\varphi| + \min(H, SN)$ and apply Haken's bound for pigeonhole formulas or the Urquhart/Ben-Sasson–Wigderson bound for Tseitin formulas on expanders.

## Depends on

- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../../proof-theory/resolution-lower-bounds/pigeonhole-formulas.md)
- [Accepted LRAT proofs refute CNF formulas](../proof-certificates/accepted-lrat-proofs-refute-cnf-formulas.md)

## Proof depends on

- [Accepted LRAT certificates translate into resolution refutations](lrat-certificates-to-resolution.md)
- [Haken's lower bound for the pigeonhole principle](../propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)
- [Urquhart: Tseitin formulas on expanders need exponential resolution refutations](../../proof-theory/tseitin-formulas/urquhart-tseitin-expander-lower-bound.md)

## Sources

- A. Haken, "The Intractability of Resolution", Theoretical Computer Science 39, 297–308, 1985.
- A. Urquhart, "Hard Examples for Resolution", Journal of the ACM 34(1), 209–219, 1987.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
