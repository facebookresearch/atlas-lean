# Waugh's birth–death interchange symmetry

Let $p_{n,m}(t\mid\lambda,\mu)$ be the probability that a linear birth–death process with per-individual birth rate $\lambda\ge 0$ and death rate $\mu\ge 0$, started from $n$ individuals, has $m$ individuals after time $t\ge 0$.

**Theorem (Waugh 1958).** For all $\lambda,\mu\ge 0$ and $n\ge 1$,

$$p_{n,n}(t\mid\lambda,\mu)=p_{n,n}(t\mid\mu,\lambda).$$

More generally, with $\tilde p_{n,m}(t\mid\lambda,\mu):=\lambda^n\mu^m\,p_{n,m}(t\mid\lambda,\mu)$, for all $m\ge 0$ and $n\ge 1$,

$$\tilde p_{n,m}(t\mid\lambda,\mu)=\tilde p_{n,m}(t\mid\mu,\lambda).$$

In particular, the probability that one individual has exactly one descendant after time $t$ is the same in a process with births at rate $\lambda$ and deaths at rate $\mu$ as in the process with the two rates swapped.

## Expansion

For $n=m=1$ the paper gives a path argument: while $k\ge 1$ individuals are alive, events occur at total rate $k(\lambda+\mu)$, which is symmetric in the two rates, and a path from $1$ back to $1$ contains equally many births and deaths, so its weight $\lambda^j\mu^j$ is unchanged by the swap. For one ancestor, $p_{1,0}=\alpha$ and $p_{1,m}=(1-\alpha)(1-\beta)\beta^{m-1}$ ($m\ge 1$) with $\alpha=\mu(e^{rt}-1)/(\lambda e^{rt}-\mu)$, $\beta=\lambda(e^{rt}-1)/(\lambda e^{rt}-\mu)$, $r=\lambda-\mu$; swapping $\lambda\leftrightarrow\mu$ exchanges $\alpha$ and $\beta$, which gives $\lambda\mu^m p_{1,m}(t\mid\lambda,\mu)=\mu\lambda^m p_{1,m}(t\mid\mu,\lambda)$ for all $m\ge 0$. The $n$ ancestors evolve independently, so $p_{n,m}$ is a sum over $m_1+\dots+m_n=m$ of products $\prod_i p_{1,m_i}$, and the weights multiply to $\lambda^n\mu^m$.

## Sources

- T. Stadler and M. Steel, "Swapping birth and death: symmetries and transformations in phylodynamic models", Systematic Biology 68(5) (2019) 852–858, <https://doi.org/10.1093/sysbio/syz039>, PMCID PMC6701459. Theorem 1.
