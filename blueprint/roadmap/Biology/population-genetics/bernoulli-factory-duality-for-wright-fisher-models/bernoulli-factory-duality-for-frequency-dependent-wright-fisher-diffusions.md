# Bernoulli factory duality for frequency-dependent Wright–Fisher diffusions

**Setting.** A *Bernoulli factory* for $f:[0,1]\to[0,1]$ turns independent $p$-coins into one $f(p)$-coin. The Keane–O'Brien construction writes

$$f(p)=\sum_{k\ge1}\Big(\tfrac34\Big)^{k-1}\tfrac14\sum_{j=0}^{\eta(f,k)}\binom{\eta(f,k)}{j}p^j(1-p)^{\eta(f,k)-j}\,\mathbf 1\Big\{f_k\Big(\tfrac{j}{\eta(f,k)}\Big)\ge\tfrac12\Big\},$$

for explicit functions $f_k$ and finite integers $\eta(f,k)$; this needs $f$ continuous and polynomially bounded away from $0$ and $1$. Consider a Wright–Fisher population of $N$ haploids with alleles $a,A$. Each offspring copies one random parent with probability $1-\sigma/N$. Otherwise it draws $L\sim\mathrm{Geo}(1/4)$, samples $\eta(f,L)$ parents, and runs the factory, so its allele is $A$ with probability $f(\text{frequency})$. Let $Y^{(N)}_t$ be the $A$-frequency at generation $\lfloor Nt\rfloor$.

**Theorem.**

1. If $f$ is also Lipschitz, then $Y^{(N)}\Rightarrow Y$ in the Skorokhod topology, where

$$dY_t=\sigma\big(f(Y_t)-Y_t\big)\,dt+\sqrt{Y_t(1-Y_t)}\,dW_t .$$

2. The number $A_t$ of ancestral lineages of a sample is a branching–coalescing Markov chain with generator

$$Gh(n)=\binom n2\big[h(n-1)-h(n)\big]+\sigma n\sum_{k\ge1}\Big(\tfrac34\Big)^{k-1}\tfrac14\big[h(n+\eta(f,k)-1)-h(n)\big].$$

3. *(Duality.)* Let $\mathbf B_n(y)$ be the vector of Bernstein polynomials of degree $n$. There is a vector-valued process $V_t$, carried along this ancestral process, such that

$$\mathbb E\big[\langle\mathbf B_n(Y_t),\mathbf v\rangle\,\big|\,Y_0=y\big]=\mathbb E\big[\langle\mathbf B_{\dim(\mathbf V_t)-1}(y),\mathbf V_t\rangle\,\big|\,\mathbf V_0=\mathbf v\big].$$

4. *(Allen–Cahn.)* In the branching Brownian motion representation of $\partial_tu-\Delta u=\lambda f(u)$ on a Lipschitz domain with Neumann boundary conditions, each branching event uses the Bernoulli factory as a voting rule among the offspring. Then the probability $\mathbb P(F(x,t)=A)$ that the root at $x$ ends up with allele $A$ solves the equation. This extends the voting construction for the Allen–Cahn nonlinearity $\varepsilon^{-2}u(1-u)(2u-1+\nu\varepsilon)$ used in spatial models of hybrid zones, where an internal branch takes the majority vote of its three children with a small correction, to any continuous, polynomially bounded $f$.

## Expansion

Classical moment duality matches $\mathbb E[Y_t^n]$ with a coalescent. For a general drift $\sigma(f(y)-y)$, the generator applied to $y^n$ gives $f(y)y^{n-1}$, which is not a polynomial unless $f$ is. Writing $f$ as a convergent mixture of Bernstein polynomials of degrees $\eta(f,k)$ with weights $(3/4)^{k-1}/4$ solves this. Each "selective" event replaces one lineage by $\eta(f,k)$ lineages, so the dual stays in the class of Bernstein-polynomial expectations, now with a type vector tracking which coin outcomes produce $A$. Any frequency-dependent selection, mutation or dominance scheme with such an $f$ therefore has an ancestral process made of coalescence and finite multi-branching. In spatial models, this gives a probabilistic, genealogical solution of reaction–diffusion equations with general reaction terms.

## Sources

- J. Koskela, K. Łatuszyński, D. Spanò, "Bernoulli factories and duality in Wright–Fisher and Allen–Cahn models of population genetics", arXiv:2306.03539 (2023): Section 2 (Keane–O'Brien factory), Theorem 1 (diffusion limit), Theorem 2 (ancestral process), Theorem 3 (Bernstein duality), Theorem 4 (Allen–Cahn representation). <https://doi.org/10.48550/arXiv.2306.03539>
