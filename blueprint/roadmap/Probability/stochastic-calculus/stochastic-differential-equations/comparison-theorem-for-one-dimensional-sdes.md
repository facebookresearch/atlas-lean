# Comparison theorem for one-dimensional stochastic differential equations

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space carrying an $(\mathcal F_t)$-Brownian motion $B$. Let $\sigma:\mathbb R\to\mathbb R$ satisfy $\lvert\sigma(x)-\sigma(y)\rvert\le h(\lvert x-y\rvert)$ for all $x,y$, where $h:[0,\infty)\to[0,\infty)$ is strictly increasing with $h(0)=0$ and $\int_0^\varepsilon h(u)^{-2}\,du=\infty$ for every $\varepsilon>0$. Let $b_1,b_2:\mathbb R\to\mathbb R$ be continuous with $b_1(x)\le b_2(x)$ for every $x$, at least one of them Lipschitz. For $i=1,2$ let $X^i$ be a continuous adapted process with

$$X^i_t=X^i_0+\int_0^t\sigma(X^i_s)\,dB_s+\int_0^tb_i(X^i_s)\,ds\qquad(t\ge0),$$

and suppose $X^1_0\le X^2_0$ almost surely. Then $\mathbb P\bigl(X^1_t\le X^2_t\text{ for all }t\ge0\bigr)=1$.

## Proof depends on

- [Yamada–Watanabe approximating functions](yamada-watanabe-approximating-functions-determin.md)

## Expansion

A proof page must apply Itô's formula to $\varphi_n\bigl((X^1_t-X^2_t)^+\bigr)$ for the [Yamada–Watanabe approximating functions](yamada-watanabe-approximating-functions-determin.md) restricted to the positive half-line, after localizing so that the stochastic integrals are martingales; show that the second-order term is at most $t/n$ by the bound $\varphi_n''\le2/(nh^2)$ and the condition on $\sigma$; bound the drift term on $\{X^1>X^2\}$ by $L\int_0^t(X^1_s-X^2_s)^+\,ds$ using $b_1\le b_2$ and the Lipschitz constant $L$ of $b_1$ or $b_2$; let $n\to\infty$; and conclude $\mathbb E(X^1_t-X^2_t)^+=0$ by Gronwall's inequality, then for all $t$ simultaneously by continuity of the paths.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer, 1999, Chapter IX, Section 3.
- N. Ikeda and S. Watanabe, *Stochastic Differential Equations and Diffusion Processes*, 2nd ed., North-Holland, 1989, Chapter VI.
