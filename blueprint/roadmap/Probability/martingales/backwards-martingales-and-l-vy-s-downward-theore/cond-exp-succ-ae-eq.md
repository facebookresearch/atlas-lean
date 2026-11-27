# Conditioning a backwards martingale on the next level

Let $\mu$ be a finite measure on $(\Omega, \mathcal{F})$, let $(\mathcal{F}_n)_{n \in \mathbb{N}}$
be a decreasing sequence of sub-$\sigma$-algebras of $\mathcal{F}$, and let $(M_n)$ be a
[backwards martingale](is-backwards-martingale.md) for $(\mathcal{F}_n)$. Then for every $n$,
$\mathbb{E}[M_n \mid \mathcal{F}_{n+1}] = M_{n+1}$ almost everywhere.
