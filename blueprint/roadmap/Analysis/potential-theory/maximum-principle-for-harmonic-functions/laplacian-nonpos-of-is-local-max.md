# The Laplacian is nonpositive at an interior maximum

Let $E$ be a finite-dimensional real inner product space and let $f : E \to \mathbb{R}$ be $C^2$
at a local maximum $z$. Then $\Delta f(z) \le 0$, where $\Delta f(z)$ is the trace of the second derivative $D^2 f(z)$.

This is the pointwise fact behind every classical maximum principle: at an interior maximum the
second derivative is negative semidefinite, so its trace is nonpositive.

## Informally uses

- [Nonpositive second derivatives at a local maximum](iterated-fderiv-two-nonpos-of-is-local-m.md):
  each term $D^2 f(z)(e_i, e_i)$ of the trace over an orthonormal basis is nonpositive.

## Sources

- L. C. Evans, *Mathematics 170: Mathematical Methods for Optimization, Finite Dimensional Optimization*, lecture notes, Spring 2021 version, [math.berkeley.edu/~evans](https://math.berkeley.edu/~evans/), §1.1.2, Theorem 1.1.2 and Remark (ii). Applied to $-f$ and summed over an orthonormal basis.
- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 3 (Laplace equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf), proof of Theorem 3.13, which uses the negative semidefinite Hessian at an interior maximum
  in the same way.
