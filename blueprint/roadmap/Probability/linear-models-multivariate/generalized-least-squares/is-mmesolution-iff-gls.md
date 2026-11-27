# The MME solution is the GLS estimate and the BLUP

Let $X$, $Z$ be real $n \times p$ and $n \times q$ matrices, let $G$ and $R$ be positive definite, let $V = Z G Z^\top + R$, and suppose that $X^\top V^{-1} X$ is invertible. Then for all $y$, $b$ and $u$, the pair $(b, u)$ [solves the mixed-model equations](is-mmesolution.md) if and only if

- $b = (X^\top V^{-1} X)^{-1} X^\top V^{-1} y$, the generalized least-squares estimate, and
- $u = G Z^\top V^{-1} (y - X b)$

(Henderson 1975).

## Sources

- C. R. Henderson, *Best linear unbiased estimation and prediction under a selection model*, Biometrics 31 (1975), 423–447.
