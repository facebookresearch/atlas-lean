# LRAT acceptance is invariant under injective renaming

Let $g$ be an injective map on variables. An LRAT certificate $\pi$ is accepted for a CNF formula $\varphi$ if and only if the certificate $g(\pi)$, obtained by renaming every literal along $g$, is accepted for $g(\varphi)$. Hence a solver may work on a densely renumbered copy of a formula (variables $0,\dots,k-1$ in order of first occurrence) and translate its certificate back.

## Proof sketch

The checker only compares literals for equality and looks clauses up by number; an injective renaming preserves both, so every propagation step behaves identically.

## Depends on

- [Accepted LRAT proofs refute CNF formulas](../accepted-lrat-proofs-refute-cnf-formulas.md)

## Sources

- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
