# Constant rank theorem

Let $d,m,r\in\mathbb N$, let $n\ge1$ be a smoothness order (finite, $\infty$ or analytic), let $U\subseteq\mathbb R^d$ be open with $x\in U$, and let $f:\mathbb R^d\to\mathbb R^m$ be $C^n$ on $U$ with $\operatorname{rank}Df(y)=r$ for all $y$ in a neighbourhood of $x$. Then there are $C^n$ charts $\varphi$ of $\mathbb R^d$ and $\psi$ of $\mathbb R^m$ (open partial homeomorphisms that are $C^n$ with $C^n$ inverses on their sources and targets) with $x\in\operatorname{source}\varphi\subseteq U$, $\varphi(x)=0$, $\psi(f(x))=0$ and $f(\operatorname{source}\varphi)\subseteq\operatorname{source}\psi$, such that

$$\psi\bigl(f(\varphi^{-1}(u))\bigr)=(u_1,\ldots,u_r,0,\ldots,0)\qquad\text{for every }u\in\operatorname{target}\varphi,$$

and for every $y\in\operatorname{source}\varphi$ the chart $\varphi$ maps the local fibre $\operatorname{source}\varphi\cap f^{-1}(f(y))$ onto the slice $\{u\in\operatorname{target}\varphi: u_i=\varphi(y)_i\text{ for }i\le r\}$. The rank hypothesis forces $r\le\min(d,m)$. Rank $r$ at the single point $x$ is not enough: the rank must be constant on a neighbourhood.
