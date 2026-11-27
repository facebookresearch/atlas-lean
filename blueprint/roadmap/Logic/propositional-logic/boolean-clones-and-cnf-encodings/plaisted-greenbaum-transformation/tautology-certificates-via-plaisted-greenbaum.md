# Tautology certificates via Plaisted–Greenbaum and clausal refutations

Let $A$ be a propositional formula over atoms $x_1,\dots,x_n$. If some LRAT certificate accepted by a sound LRAT checker refutes the CNF formula $\mathrm{PG}(\neg A)$ (with numbered definition variables), then $A$ is a tautology: it is true under every Boolean assignment of $x_1,\dots,x_n$. Consequently a SAT solver that emits LRAT refutations, combined with a sound LRAT checker, yields a sound tautology prover whose certificates are checked against a clause form of linear size; it is also complete when the solver returns a refutation for every unsatisfiable input, as every unsatisfiable CNF formula has an LRAT refutation.

## Proof sketch

An accepted LRAT certificate shows that $\mathrm{PG}(\neg A)$ has no model; by equisatisfiability $\neg A$ has no model, so $A$ is valid.

## Depends on

- [Plaisted–Greenbaum clause form](plaisted-greenbaum-clause-form.md)
- [Accepted LRAT proofs refute CNF formulas](../../proof-certificates/accepted-lrat-proofs-refute-cnf-formulas.md)

## Proof depends on

- [Plaisted–Greenbaum: the polarity-aware clause form is equisatisfiable](plaisted-greenbaum-equisatisfiability.md)
- [Every unsatisfiable CNF has an LRAT refutation](../../proof-certificates/every-unsatisfiable-cnf-has-an-lrat-refutation.md)

## Sources

- D. A. Plaisted and S. Greenbaum, "A Structure-Preserving Clause Form Translation", Journal of Symbolic Computation 2(3), 293–304, 1986.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
