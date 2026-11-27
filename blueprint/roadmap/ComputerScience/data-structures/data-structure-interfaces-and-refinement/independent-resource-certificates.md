# Independent resource certificates combine additively

If an implementation has an amortized certificate for a resource measure $\mu_1$ with charges $c_1$ and potential $\Phi_1$, and one for a measure $\mu_2$ with charges $c_2$ and potential $\Phi_2$, both relative to the same representation, then it has a certificate for $\mu_1 + \mu_2$ with charges $c_1 + c_2$ and potential $\Phi_1 + \Phi_2$; a certificate for $\mu$ also yields one for $\lambda \mu$ with charges $\lambda c$ and potential $\lambda \Phi$ for every $\lambda \ge 0$.

## Proof sketch

Add (respectively scale) the two per-operation physicist's inequalities.

## Depends on

- [Refinement of a data-structure specification by an abstraction function](refinement-by-abstraction-function.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. E. Tarjan, "Amortized Computational Complexity", SIAM Journal on Algebraic and Discrete Methods 6(2), pp. 306-318, 1985.
