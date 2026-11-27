# Composition of amortized refinements adds potentials

Let $(\alpha_1, \Phi_1)$ be an amortized refinement of $D$ by $E$ with lower charges $c_E$ and upper charges $c_D$, and let $(\alpha_2, \Phi_2)$ be an amortized refinement of $E$ by $F$ with lower charges $c_F$ and upper charges $c_E$. Then composing the methods gives an amortized refinement of $D$ by $F$ with abstraction $\alpha_1 \circ \alpha_2$ and potential

$$
\Phi(f) = \Phi_2(f) + \Phi_1(\alpha_2(f)).
$$

Consequently, for every admissible sequence of $D$-operations executed through $F$ from an initial state $f_0$ satisfying the invariant of the second refinement and whose abstraction $\alpha_2(f_0)$ satisfies the invariant of the first, the total $F$-cost is at most $\Phi(f_0)$ plus the sum of the $D$-charges.

## Proof sketch

Running a $D$-method through $F$ replaces each $E$-operation by its $F$-method. Summing the $F$-level inequality over the $E$-operations of one $D$-method telescopes $\Phi_2$ and bounds the $F$-cost by the $E$-cost plus the change of $\Phi_2$; the $E$-level inequality bounds that $E$-cost by the $D$-charge plus the change of $\Phi_1 \circ \alpha_2$. Telescoping over the whole sequence and dropping the nonnegative final potential gives the total bound. Single-valuedness of the abstraction is what makes the composed potential a function of the lowest state.

## Depends on

- [Refinement of a data-structure specification by an abstraction function](refinement-by-abstraction-function.md)

## Proof depends on

- [Potential method: amortized costs bound actual costs](../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. D. Sleator and R. E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3), pp. 652-686, 1985.
- C. A. R. Hoare, "Proof of Correctness of Data Representations", Acta Informatica 1(4), pp. 271-281, 1972.
- R. E. Tarjan, "Amortized Computational Complexity", SIAM Journal on Algebraic and Discrete Methods 6(2), pp. 306-318, 1985.
