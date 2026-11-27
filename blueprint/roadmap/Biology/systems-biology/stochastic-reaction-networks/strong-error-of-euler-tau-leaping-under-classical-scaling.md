# Strong error of Euler tau-leaping under the classical scaling

Consider a reaction network on $\mathbb R^d$ with reaction vectors $\zeta_1, \dots, \zeta_K$ and intensity functions $\lambda_1, \dots, \lambda_K : \mathbb R^d \to [0, \infty)$, and, for a system size $V \ge 1$, the process in the classical scaling given by the random time-change representation

$$X^V(t) = X^V(0) + \sum_{k=1}^K \frac{\zeta_k}{V}\, Y_k\Bigl(V\int_0^t \lambda_k(X^V(s))\,ds\Bigr),$$

with independent unit-rate Poisson processes $Y_k$. For $0 < \beta < 1$ let $h_V = V^{-\beta}$, let $\eta_V(s) = h_V\lfloor s/h_V \rfloor$, and let the Euler tau-leap process $Z^V$ be defined by the same equation with $\lambda_k(Z^V(\eta_V(s)))$ in place of $\lambda_k(X^V(s))$, driven by the same $Y_k$ and started at $Z^V(0) = X^V(0)$. Assume that every $\lambda_k$ is bounded and globally Lipschitz on $\mathbb R^d$; Anderson, Ganguly and Kurtz (2011) reduce to this case by modifying the intensities outside a compact set that contains the trajectories. Then for every $T > 0$ there is $C = C(T)$, independent of $V$, with

$$\sup_{t \le T} E\,|X^V(t) - Z^V(t)| \le C\, V^{-\beta} = C\, h_V$$

(their Theorem 3.2).

## Depends on

- [Random time-change representation of density-dependent chains](../../../Probability/markov-chains/density-dependent-markov-chains/random-time-change-representation-of-density-dep.md)

## Expansion

1. The model: random time-change representation of $X^V$, the Euler tau-leap process $Z^V$ and their coupling through common Poisson processes, with the scaling and the truncation of the intensities.
2. The strong error bound by a Grönwall argument on $E|X^V - Z^V|$, using $E|Z^V(s) - Z^V(\eta_V(s))| \le C h_V$ (Theorem 3.2).
3. Separate target: the limit of $V^\beta(X^V - Z^V)$, the exact first-order asymptotics of the error (Theorem 3.10), with its hypotheses.
4. The weak-error expansion (Theorem 4.1), and the comparison with the midpoint method, as separate statements.

## Sources

- D. F. Anderson, A. Ganguly and T. G. Kurtz, Error analysis of tau-leap simulation methods, Ann. Appl. Probab. 21 (2011), 2226–2262, Theorems 3.2, 3.10, 4.1. <https://doi.org/10.1214/10-aap756>
