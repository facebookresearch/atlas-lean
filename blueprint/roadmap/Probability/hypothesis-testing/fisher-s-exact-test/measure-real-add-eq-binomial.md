# Sum of independent binomials

Let $n_1, n_2 \in \mathbb{N}$, $p \in [0,1]$, and let $X, Y$ be independent measurable $\mathbb{N}$-valued random variables on $(\Omega, \mu)$ with laws $\mathrm{Bin}(n_1, p)$ and $\mathrm{Bin}(n_2, p)$. Then $X + Y \sim \mathrm{Bin}(n_1 + n_2, p)$: for every $t \in \mathbb{N}$,

$$\mu(X + Y = t) = \binom{n_1 + n_2}{t} p^t (1 - p)^{n_1 + n_2 - t},$$

which is $0$ for $t > n_1 + n_2$.
