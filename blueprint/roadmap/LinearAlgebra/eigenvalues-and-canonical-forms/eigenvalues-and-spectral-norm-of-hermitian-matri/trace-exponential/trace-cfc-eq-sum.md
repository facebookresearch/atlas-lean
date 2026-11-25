# Trace of a standard matrix function

Let $A$ be a Hermitian matrix over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, indexed by a finite set, with eigenvalues $\lambda_i(A)$, and let $f : \mathbb{R} \to \mathbb{R}$ be any function. The standard matrix function $f(A) = Q\,\operatorname{diag}(f(\lambda_i))\,Q^*$ (the continuous functional calculus) satisfies

$$\operatorname{tr} f(A) = \sum_i f(\lambda_i(A)).$$

The proof reads the trace off the characteristic polynomial $\prod_i (X - f(\lambda_i))$ of $f(A)$.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Definition 2.1.2 and Proposition 2.1.3.
