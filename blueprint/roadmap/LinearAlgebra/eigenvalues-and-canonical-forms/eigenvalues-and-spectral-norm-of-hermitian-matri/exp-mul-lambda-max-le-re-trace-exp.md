# Trace exponential dominates the top eigenvalue

For a Hermitian matrix $A$ indexed by a nonempty finite set and every real $\theta$,

$$e^{\theta\lambda_{\max}(A)} \le \operatorname{tr} e^{\theta A}.$$

For $\theta > 0$ this is Tropp's display (3.2.3), $e^{\lambda_{\max}(\theta A)} = \lambda_{\max}(e^{\theta A}) \le \operatorname{tr} e^{\theta A}$: the eigenvalue map passes through the increasing function $e^{\theta\,\cdot}$, and the trace of a positive-definite matrix dominates its largest eigenvalue. It is the one genuinely matrix step of the matrix Laplace transform method; Tropp notes that bounding $\lambda_{\max}$ by the trace costs at most the dimensional factor $d$, which is sometimes unavoidable.

## Informally uses

- [Trace dominates each eigenvalue of a positive-semidefinite matrix](eigenvalues-le-re-trace.md): the same domination of $\lambda_{\max}$ by the trace, here applied to the positive-definite $e^{\theta A}$.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, proof of Proposition 3.2.1, display (3.2.3).
