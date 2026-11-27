# Strong error of Euler tau-leaping under the classical scaling

Anderson, Ganguly and Kurtz (2011, Section 2) consider a reaction network with $d$ species and reactions $k = 1, \dots, K$ with source vectors $\nu^s_k$ and reaction vectors $\nu_k$, in the classical scaling: for a system size $V \ge 1$ the initial abundances scale with $V$ and the mass-action rate constants are $c^V_k = d_k/V^{\nu^s_k\cdot\mathbf 1 - 1}$ with $d_k > 0$. Let $x(t)$ be the solution of the deterministic mass-action equation (2.1) with rate constants $d_k$, and let $\gamma \ge 0$ be a $C^\infty$ function with compact support in $\mathbb R^d_{>0}$ with $\gamma(x) = 1$ for all $x \in B_r(x(t))$, for some $r > 0$. The intensities are the truncated mass-action intensities

$$\lambda^V_k(x) = \gamma(x/V)\,c^V_k\prod_{\ell=1}^d\frac{x_\ell!}{(x_\ell - \nu^s_{k\ell})!}$$

(their (2.6)), and $A^V_k(x) = V^{-1}\lambda^V_k(Vx)$; for each $k$ there is $L_k > 0$ with $\sup_{x \in \mathbb R^d,\,|\alpha| < \infty}|D^\alpha A^V_k(x)| \le L_k$ (their (2.7)). The normalized process $X^V$ satisfies the random time-change representation

$$X^V(t) = X^V(0) + \sum_{k=1}^K \frac{\nu_k}{V}\, Y_k\Bigl(V\int_0^t A^V_k(X^V(s))\,ds\Bigr)$$

with independent unit-rate Poisson processes $Y_k$ (their (3.1)). For $0 < \beta < 1$ let $h_V = V^{-\beta}$ (their (2.5)), let $\eta(s) = h_V\lfloor s/h_V \rfloor$, and let the Euler tau-leap process $Z^V$ be defined by the same equation with $A^V_k(Z^V(\eta(s)))$ in place of $A^V_k(X^V(s))$, driven by the same $Y_k$ and started at $Z^V(0) = X^V(0)$ (their (3.2)). Then for every $T > 0$ there is $C = C(T)$, independent of $V$, with

$$\sup_{t \le T} E\,|X^V(t) - Z^V(t)| \le C\, V^{-\beta} = C\, h_V$$

(their Theorem 3.2).

## Depends on

- [Random time-change representation of density-dependent chains](../../../Probability/markov-chains/density-dependent-markov-chains/random-time-change-representation-of-density-dep.md)

## Expansion

1. The model: random time-change representation of $X^V$, the Euler tau-leap process $Z^V$ and their coupling through common Poisson processes, with the classical scaling and the truncation (2.6) of the intensities by the cutoff $\gamma$, which equals $1$ near the deterministic path $x(t)$ and changes the intensities only where the process leaves the scaling regime.
2. The strong error bound by a Grönwall argument on $E|X^V - Z^V|$, using $E|Z^V(s) - Z^V(\eta(s))| \le C h_V$ (Theorem 3.2).
3. Separate target: the limit of $V^\beta(X^V - Z^V)$, the exact first-order asymptotics of the error (Theorem 3.10), with its hypotheses.
4. The weak-error expansion (Theorem 4.1), and the comparison with the midpoint method, as separate statements.

## Sources

- D. F. Anderson, A. Ganguly and T. G. Kurtz, Error analysis of tau-leap simulation methods, Ann. Appl. Probab. 21 (2011), 2226–2262, Section 2 (equations (2.1), (2.5)–(2.7)), equations (3.1)–(3.2), Theorems 3.2, 3.10, 4.1. <https://doi.org/10.1214/10-aap756>
