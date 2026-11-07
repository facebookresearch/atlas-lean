# Green's theorem

Let $U \subseteq \mathbb{R}^2$ be open, let $D \subseteq U$ be bounded and
measurable, and let $L, M : \mathbb{R}^2 \to \mathbb{R}$ be continuously differentiable on $U$.
Let $a\lt b$ and let $\gamma=(\gamma_1,\gamma_2) : \mathbb{R} \to \mathbb{R}^2$ be continuous on
$[a,b]$, with $\gamma(a)=\gamma(b)$, injective on $[a,b)$, with $\gamma(t)\ne\gamma(a)$ for
$a\lt t\lt b$, with image $\gamma([a,b])$ equal to the boundary of $D$, and with $\gamma(t)\in U$ for
all $t\in[a,b]$. Suppose there is a finite set $S\subseteq[a,b]$ containing $a$ and $b$ such that
$\gamma$ is continuously differentiable on $[a,b]\setminus S$ and on $[u,v]$ for any two
consecutive points $u\lt v$ of $S$, and such that for every $t\in(a,b)\setminus S$ we have
$\gamma'(t)\ne0$ and, for some $\delta>0$, $\gamma(t)+\varepsilon(-\gamma_2'(t),\gamma_1'(t))\in D$
for all $0\lt \varepsilon\lt \delta$ (so $D$ lies to the left of the curve). Then

$$
\int_a^b \bigl(L(\gamma(t))\,\gamma_1'(t)+M(\gamma(t))\,\gamma_2'(t)\bigr)\,dt
=\int_D \Bigl(\frac{\partial M}{\partial x}-\frac{\partial L}{\partial y}\Bigr)\,d(x,y).
$$

## Sources

- https://en.wikipedia.org/wiki/Green%27s_theorem (greens-theorem-s1).
