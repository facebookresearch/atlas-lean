# Global stability of the SIS patch endemic equilibrium with equal migration rates

**Setting.** Consider the deterministic SIS patch model

$$\frac{ds_j}{dt} = -\lambda_j\frac{s_j i_j}{s_j+i_j} + \gamma_j i_j + \nu_S\sum_{k\neq j}\big(a_{kj}s_k - a_{jk}s_j\big),\qquad \frac{di_j}{dt} = \lambda_j\frac{s_j i_j}{s_j+i_j} - \gamma_j i_j + \nu_I\sum_{k\neq j}\big(a_{kj}i_k - a_{jk}i_j\big),$$

$j = 1,\dots,\ell$, with $\lambda_j, \gamma_j > 0$ and an irreducible, symmetric connectivity matrix $A = (a_{ij})$. Let $\Lambda = \operatorname{diag}(\lambda_j)$, $\Gamma = \operatorname{diag}(\gamma_j)$, and let $D$ be the matrix with $d_{ij} = a_{ij}$ for $i \ne j$ and $d_{ii} = -\sum_{k\ne i} a_{ik}$. With $V = \nu_I D - \Gamma$, the basic reproduction number is

$$\mathcal{R}_0 = \rho(-\Lambda V^{-1}).$$

The disease-free equilibrium is $(s_j, i_j) = (1/\ell, 0)$ for all $j$; it is globally asymptotically stable when $\mathcal{R}_0 < 1$.

**Theorem.** Assume $\nu_I = \nu_S =: \nu$ and $\mathcal{R}_0 > 1$. Then the system has a unique endemic equilibrium $z^* = (s_1^*, i_1^*, \dots, s_\ell^*, i_\ell^*)$ with $i^* \gg 0$, and $z^*$ is globally asymptotically stable for initial data with a nonzero infectious population.

## Expansion

With equal migration rates the patch totals $n_j = s_j + i_j$ satisfy the closed linear system $n' = \nu D n$, an irreducible Markov-chain forward equation with a unique globally attracting positive equilibrium $n^*$. The full system is triangular, so by Vidyasagar's theorem on triangular systems it suffices to study the limiting infectious system

$$i' = (\nu D - \Gamma + \Lambda)\,i - \operatorname{diag}(1/n_j^*)\operatorname{diag}(i)\,\Lambda i .$$

Its Jacobian is an irreducible Metzler matrix that is strictly decreasing in $i$, so Hirsch's theorem for strongly monotone, sublinear systems gives the dichotomy: either all trajectories tend to $0$, or there is a unique interior equilibrium attracting all nonzero trajectories. By Varga's theorem, $\mathcal{R}_0 > 1$ is equivalent to the stability modulus $\alpha(\Lambda + V) > 0$, which rules out the first alternative. At $i^*$ the Jacobian $J$ satisfies $J i^* < 0$, so it is Hurwitz and the equilibrium is locally stable as well. The paper also notes that the disease-free equilibrium remains globally stable at $\mathcal{R}_0 = 1$ under $\nu_I = \nu_S$, using the linear Lyapunov function $\langle v, i\rangle$ with $v$ a positive left null vector of $\Lambda + V$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Sources

- T. Yeo, "Stochastic and deterministic SIS patch model", arXiv:2007.07583 (2020), Proposition 3.1, Lemmas 3.1–3.3 and Theorem 3.3, <https://doi.org/10.48550/arXiv.2007.07583>.
- L. J. S. Allen, B. M. Bolker, Y. Lou and A. L. Nevai, "Asymptotic profiles of the steady states for an SIS epidemic patch model", SIAM J. Appl. Math. 67 (2007).
