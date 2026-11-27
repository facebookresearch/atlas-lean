# Counting models of DNF formulas is #P-complete

The function that maps a DNF formula $\varphi$ to its model count is $\#\mathsf{P}$-complete under polynomial-time Turing reductions (one oracle query followed by a subtraction suffices), although satisfiability of DNF formulas is decidable in polynomial time (a DNF formula is satisfiable iff some term contains no complementary pair). Indeed the model count of a DNF formula on $n$ variables is $2^n$ minus the model count of the CNF formula obtained by negating it.

## Proof sketch

The negation map turns a CNF formula into a DNF formula with complementary model count, so $\#\mathrm{SAT}$ reduces to $\#\mathrm{DNF}$ by one subtraction; membership in $\#\mathsf{P}$ is immediate.

## Depends on

- [Disjunctive normal form](disjunctive-normal-form.md)
- [Model count of a CNF formula](../../model-count-preserving-cnf-transformations/model-count.md)

## Proof depends on

- [Counting SAT is #P-complete](../../../../TheoryOfComputation/counting-complexity/counting-satisfiability-sat/count-sat-sharp-p-complete.md)

## Sources

- L. G. Valiant, "The Complexity of Enumeration and Reliability Problems", SIAM Journal on Computing 8(3), 410–421, 1979.
- R. M. Karp, M. Luby and N. Madras, "Monte-Carlo Approximation Algorithms for Enumeration Problems", Journal of Algorithms 10(3), 429–448, 1989.
