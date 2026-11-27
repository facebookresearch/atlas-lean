# Linear-time LRAT checking on the word RAM

Assume that variables and clause identifiers are positive integers at most the input length $L$ (for example, numbered consecutively). There is a deterministic word-RAM program that, given an encoded CNF formula $\varphi$ and an encoded LRAT certificate $\pi$ (RUP steps with hints, and deletions; RAT steps are rejected), halts with output $1$ exactly when the LRAT checker accepts $\pi$ for $\varphi$ and with $0$ otherwise, within $O(L + W)$ instructions, where $L$ is the input length in words and $W$ is the total length of the clauses named by the hints. Since $W$ is at most the number of hints times the maximum clause width $w$, the running time is $O(F + C \cdot \max(1, w))$ for $F$ and $C$ the encoded lengths of formula and certificate.

## Proof sketch

Keep a clause database indexed by clause identifier and an assignment array. For each step, assign the negation of the new clause, then scan each hinted clause once to check that it is unit (and propagate) or falsified at the last hint; undo the assignment afterwards. Every hinted clause is read once per occurrence. Direct addressing by variable and identifier, which the bound on their values allows, replaces the balanced search structures of the published analysis, whose bound carries logarithmic factors.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/rup-and-rat-clauses.md)

## Proof depends on

- [Accepted LRAT proofs refute CNF formulas](../../../Logic/propositional-logic/proof-certificates/accepted-lrat-proofs-refute-cnf-formulas.md)

## Sources

- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017, Section 4: the checking algorithm (Algorithms check_RAT and check_LRAT) and its complexity analysis (Lemma 2), with logarithmic overheads.
