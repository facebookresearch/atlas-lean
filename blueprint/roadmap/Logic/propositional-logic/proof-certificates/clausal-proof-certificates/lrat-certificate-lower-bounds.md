# Exponential lower bounds for LRAT certificates

There is a family of unsatisfiable $O(1)$-CNF formulas with $O(n)$ variables and clauses (Tseitin formulas on expanders) all of whose accepted LRAT certificates (without extension or RAT steps) have length $2^{\Omega(n)}$; [CDCL certificates of pigeonhole formulas are exponential](../../../../ComputerScience/heuristic-search-and-planning/dpll-certificates-and-size-bounds/cdcl-pigeonhole-certificate-lower-bound.md) gives a second such family, with $\Theta(n^2)$ variables. These bound the certificate, regardless of the solver that produced it.

## Proof sketch

Translate an accepted certificate into a resolution refutation of size at most $|\varphi| + \min(H, SN)$ and apply the Urquhart/Ben-Sasson–Wigderson bound for Tseitin formulas on expanders: with $|\varphi|, N = O(n)$ the number of steps is at least $(2^{cn} - O(n))/O(n) = 2^{\Omega(n)}$.

## Depends on

- [Accepted LRAT proofs refute CNF formulas](../accepted-lrat-proofs-refute-cnf-formulas.md)

## Proof depends on

- [CDCL certificates of pigeonhole formulas are exponential](../../../../ComputerScience/heuristic-search-and-planning/dpll-certificates-and-size-bounds/cdcl-pigeonhole-certificate-lower-bound.md)

- [Accepted LRAT certificates translate into resolution refutations](lrat-certificates-to-resolution.md)
- [Urquhart: Tseitin formulas on expanders need exponential resolution refutations](../../../proof-theory/tseitin-formulas/urquhart-tseitin-expander-lower-bound.md)

## Sources

- A. Urquhart, "Hard Examples for Resolution", Journal of the ACM 34(1), 209–219, 1987.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Corollary 4.5.
