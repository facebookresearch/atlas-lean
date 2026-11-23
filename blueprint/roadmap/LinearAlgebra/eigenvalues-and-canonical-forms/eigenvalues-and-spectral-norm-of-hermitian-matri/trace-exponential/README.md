# Trace exponential of a Hermitian matrix

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $A$ be a Hermitian matrix over $\mathbb{K}$ indexed by a finite set, with eigenvalues $\lambda_i(A)$, and let $\theta$ be real. Then

$$\operatorname{tr} e^{\theta A} = \sum_i e^{\theta \lambda_i(A)}.$$

## Idea

For a Hermitian matrix, the power-series exponential agrees with the matrix function obtained by applying $x \mapsto e^{\theta x}$ to the eigenvalues in an orthonormal eigenbasis, and the trace of any such function is the sum of the function over the eigenvalues. So the trace exponential is a sum of positive terms, one per index: it is nonnegative, positive when the index set is nonempty, and it dominates $e^{\theta \lambda_i}$ for each eigenvalue, in particular $e^{\theta \lambda_{\max}}$ when there is an eigenvalue. This simple bound is the starting point of the matrix Laplace-transform method: to bound $\lambda_{\max}$ of a random Hermitian matrix one bounds the expected trace exponential, as in the matrix Chernoff and Bernstein inequalities.

## Statements

- [Trace exponential in terms of eigenvalues](trace-exp-smul-eq-sum.md)
- [Trace of a standard matrix function](trace-cfc-eq-sum.md): the general form, for any function of the eigenvalues
- [The matrix exponential is a standard matrix function](exp-smul-eq-cfc.md): the exponential as a function of the eigenvalues
- [Real trace exponential in terms of eigenvalues](re-trace-exp-smul-eq-sum.md): the same identity for the real part
- [Nonnegativity of the trace exponential](re-trace-exp-nonneg.md): the trace exponential is nonnegative
- [Positivity of the trace exponential](re-trace-exp-pos.md): and positive for a nonempty index set
- [Trace exponential dominates each eigenvalue](exp-mul-eigenvalues-le-re-trace-exp.md): it dominates each $e^{\theta \lambda_i}$
- [Trace exponential dominates the top eigenvalue](exp-mul-lambda-max-le-re-trace-exp.md): it dominates $e^{\theta \lambda_{\max}}$
- [Trace exponential dominates the bottom eigenvalue](exp-mul-lambda-min-le-re-trace-exp.md): it dominates $e^{\theta \lambda_{\min}}$
