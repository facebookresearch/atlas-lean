# Every unsatisfiable CNF has an LRAT refutation

Use the LRAT addition and deletion steps and their checker from
[LRAT addition steps certify RUP and RAT clauses](lrat-addition-steps-certify-rup-and-rat-clauses.md). If a CNF formula $F$ is
unsatisfiable, then $F$ has an LRAT proof that the checker accepts and that ends by adding the empty clause, using only addition
steps accepted by positive hints.

Proof: $F$ has a resolution refutation, a sequence of clauses ending with the empty clause in which every clause is a clause of $F$,
the resolvent $R$ on a variable $x$ of two earlier clauses $C \ni x$ and $D \ni \neg x$, or a weakening $E$ of an earlier clause $C \subseteq E$.
Add the derived clauses in order. For a resolvent, give the hints $C, D$: every literal of $C$ other than $x$ lies in $R$, so
$C \setminus R = \{x\}$ and $\neg x$ is appended; then every literal of $D$ is $\neg x$ or lies in $R$, so $D$ minus the current list is empty and the
step is accepted. For a weakening, the single hint $C$ gives $C \setminus E = \emptyset$. The proof has one addition step per derived clause.

## Depends on

- [LRAT addition steps certify RUP and RAT clauses](lrat-addition-steps-certify-rup-and-rat-clauses.md)

## Proof depends on

- [Refutation completeness](../resolution/resolution-derivable-nil-of-not-cnf-sat.md)
- [Resolution refutation](../resolution-size-and-width/is-resolution-refutation.md)

## Sources

- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient certified RAT verification", *CADE 2017*, LNCS 10395, Springer, 2017, <http://www.cs.cmu.edu/~mheule/publications/lrat.pdf>: Section 4 (algorithm check_RAT, step 3). The translation from resolution refutations is derived on this page.
