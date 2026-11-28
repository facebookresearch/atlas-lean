# Adhesion velocity as an averaged gradient

Let $\Omega\subset\mathbb R^n$ be a bounded smooth domain, $B_r$ the open ball of radius $r$ about $0$, $\Omega_r=\{x\in\Omega:\operatorname{dist}(x,\partial\Omega)>r\}$, and let $F_r(\rho)$ be continuous and positive on $[0,r_0]^2$ with $F_0(0)=n+1$. Extending functions by zero outside $\Omega$, the adhesion velocity of $u$ is

$$\mathcal A_ru(x)=\frac{1}{r\,|B_r|}\int_{B_r}u(x+\xi)\,F_r(|\xi|)\,\frac{\xi}{|\xi|}\,d\xi,$$

and the averaging operator on vector fields $w$ is

$$\mathcal T_rw(x)=\frac{1}{r\,|B_r|}\int_0^1\!\!\int_{B_r}F_r(|\xi|)\,\frac{\xi}{|\xi|}\big(\xi\cdot w(x+s\xi)\big)\,d\xi\,ds .$$

Then:

1. for $u\in W^{1,1}(\Omega)$ and $r\in(0,r_0]$, $\mathcal A_ru=\mathcal T_r(\nabla u)$ almost everywhere in $\Omega_r$;
2. $\mathcal T_r$ is a bounded linear operator on $(L^p(\Omega))^n$ for every $p\in[1,\infty]$, and for $p\in[1,\infty]$ with conjugate exponent $p'$ (so $1/p+1/p'=1$) it is symmetric with respect to the $L^p$–$L^{p'}$ pairing: $\int_\Omega\mathcal T_rw_1\cdot w_2\,dx=\int_\Omega w_1\cdot\mathcal T_rw_2\,dx$ for all $w_1\in(L^p(\Omega))^n$ and $w_2\in(L^{p'}(\Omega))^n$; for $p=2$ this is self-adjointness on the Hilbert space $(L^2(\Omega))^n$;
3. for $p\in[1,\infty)$ and $w\in(L^p(\Omega))^n$, $\mathcal T_rw\to w$ in $(L^p(\Omega))^n$ as $r\to0$, and $\|\mathcal T_r\|_{\mathcal L((L^2)^n)}\to1$.

## Expansion

By symmetry $\int_{B_r}F_r(|\xi|)\xi/|\xi|\,d\xi=0$, so $u(x)$ may be subtracted inside $\mathcal A_r$, and $u(x+\xi)-u(x)=\int_0^1\nabla u(x+s\xi)\cdot\xi\,ds$ gives the representation when the ball stays inside $\Omega$. The normalisation $F_0(0)=n+1$ makes $\mathcal T_0$ the identity, because $\frac{1}{r|B_r|}\int_{B_r}|\xi|\,\frac{\xi\otimes\xi}{|\xi|^2}\,d\xi=\frac{1}{n+1}I$. Averaging $\nabla u$ instead of $u$ matters at the boundary: for $u\equiv1$ on $(-1,1)$ and $F_r\equiv2$, $\mathcal A_ru$ has $L^1$ norm $1$ concentrated in the layer $\Omega\setminus\Omega_r$, so it converges to $u'=0$ in measure but not in $L^1$, while $\mathcal T_r(u')\equiv0$.

## Sources

- M. Eckardt, K. J. Painter, C. Surulescu, A. Zhigun, "Nonlocal and local models for taxis in cell migration: a rigorous limit procedure", J. Math. Biol. 81 (2020), Section 3, Lemma 3.1, Example 3.3 and Lemma 3.5, <https://doi.org/10.1007/s00285-020-01536-4>, PMCID PMC7716906.
