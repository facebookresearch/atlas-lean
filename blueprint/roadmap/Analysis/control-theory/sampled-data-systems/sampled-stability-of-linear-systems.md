# Stability is preserved by exact sampling

Let $A \in \mathbb{C}^{n \times n}$ (or $\mathbb{R}^{n \times n}$) and $T > 0$. Then $A$ is Hurwitz (every eigenvalue has negative real part) if and only if $e^{TA}$ is convergent (every eigenvalue has modulus less than $1$).

By the spectral mapping theorem, the eigenvalues of $e^{TA}$ are exactly the numbers $e^{T\lambda}$ with $\lambda$ an eigenvalue of $A$. Since $|e^{T\lambda}| = e^{T \operatorname{Re} \lambda}$ and $T > 0$, we have $|e^{T\lambda}| < 1$ if and only if $\operatorname{Re} \lambda < 0$.

For complex coefficients, the decay conclusions follow by the same Jordan-form argument, or by realifying the system.

Hence the exact sampled system $x_{k+1} = e^{TA} x_k$ of $\dot x = A x$ at period $T$, which is the zero-order-hold discretization with zero input, is exponentially stable exactly when the continuous-time system is.

## Proof depends on

- [Exponential stability of linear differential equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md): Hurwitz matrices are those whose flow decays
- [Exponential stability of linear difference equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-difference-equations.md): convergent matrices are those whose powers decay

- [Jordan normal form](../../../LinearAlgebra/eigenvalues-and-canonical-forms/jordan-normal-form/exists-jordan-normal-form-of-splits.md): finite-dimensional spectral mapping for the matrix exponential

## Background

- [Zero-order-hold sampling of a linear time-invariant system](zero-order-hold-sampled-system.md): $e^{TA}$ is the state matrix of the sampled system

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Appendix A.3, Lemma/Exercise A.3.2 and its spectral-mapping consequence (pp. 453–454), and Section 3.4, proof of Theorem 4 (p. 102): by the Spectral Mapping Theorem the eigenvalues of $e^{\delta A}$ are the numbers $e^{\delta\lambda}$ for eigenvalues $\lambda$ of $A$; Hurwitz and convergent matrices as in Appendix C.5, Proposition C.5.1 (pp. 491–492).
