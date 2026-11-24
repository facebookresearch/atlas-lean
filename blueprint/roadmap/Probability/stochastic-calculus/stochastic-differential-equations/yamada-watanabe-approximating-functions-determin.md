# Yamada–Watanabe approximating functions

Let $h:[0,\infty)\to[0,\infty)$ be continuous and strictly increasing with $h(0)=0$, and suppose that for every $\varepsilon>0$

$$\int_0^\varepsilon\frac{du}{h(u)^2}=\infty$$

as an extended-real Lebesgue integral. Then there is a strictly decreasing sequence $a_0=1>a_1>a_2>\dots$ with $a_n\to0$ and

$$\int_{a_n}^{a_{n-1}}\frac{du}{h(u)^2}=n\qquad(n\ge1),$$

and there are even functions $\varphi_n\in C^2(\mathbb R)$ such that $\varphi_n(x)\to|x|$ for every $x$, $|\varphi_n'|\le1$, and

$$0\le\varphi_n''(x)\le\frac{2}{n\,h(|x|)^2}\qquad(x\ne0),$$

with $\varphi_n''$ supported in $\{a_n<|x|<a_{n-1}\}$. For $h(u)=\sqrt u$ one may take $a_n=e^{-n(n+1)/2}$, since $\int_{a_n}^{a_{n-1}}du/u=\log(a_{n-1}/a_n)=n$.

## Expansion

A full proof chooses $a_n$ by continuity and divergence of $u\mapsto\int_u^{a_{n-1}}h^{-2}$, picks a continuous $\psi_n\ge0$ supported in $(a_n,a_{n-1})$ with $\psi_n\le2/(n\,h^2)$ and $\int\psi_n=1$ (possible because $\int_{a_n}^{a_{n-1}}2/(nh^2)=2$), and sets $\varphi_n(x)=\int_0^{|x|}\int_0^y\psi_n(u)\,du\,dy$. Then $|x|-a_{n-1}\le\varphi_n(x)\le|x|$, which gives the convergence.

It also uses:

- The fundamental theorem of calculus and continuous bump functions with prescribed integral

## Sources

- T. Yamada and S. Watanabe, *On the uniqueness of solutions of stochastic differential equations*, J. Math. Kyoto Univ. 11 (1971), 155–167, approximation of $|x|$ used in the uniqueness proof.
