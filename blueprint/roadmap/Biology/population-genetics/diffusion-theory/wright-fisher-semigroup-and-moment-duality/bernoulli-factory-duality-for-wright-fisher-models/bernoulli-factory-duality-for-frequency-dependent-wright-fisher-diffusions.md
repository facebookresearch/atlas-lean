# Bernoulli factory duality for frequency-dependent Wright–Fisher diffusions

**Setting.** A *Bernoulli factory* for $f:[0,1]\to[0,1]$ turns independent $p$-coins into one $f(p)$-coin. The Keane–O'Brien construction writes

$$f(p)=\sum_{k\ge1}\Big(\tfrac34\Big)^{k-1}\tfrac14\sum_{j=0}^{\eta(f,k)}\binom{\eta(f,k)}{j}p^j(1-p)^{\eta(f,k)-j}\,\mathbf 1\Big\{f_k\Big(\tfrac{j}{\eta(f,k)}\Big)\ge\tfrac12\Big\},$$

for explicit functions $f_k$ and finite integers $\eta(f,k)$; this needs $f$ continuous and polynomially bounded away from $0$ and $1$. Consider a Wright–Fisher population of $N$ haploids with alleles $a,A$. Each offspring copies one random parent with probability $1-\sigma/N$. Otherwise it draws $L\sim\mathrm{Geo}(1/4)$, samples $\eta(f,L)$ parents, and runs the factory, so its allele is $A$ with probability $f(\text{frequency})$. Let $Y^{(N)}_t$ be the $A$-frequency at generation $\lfloor Nt\rfloor$.

**Theorem.**

1. If $f$ is also Lipschitz, then $Y^{(N)}\Rightarrow Y$ in the Skorokhod topology, where

    $$dY_t=\sigma\big(f(Y_t)-Y_t\big)\,dt+\sqrt{Y_t(1-Y_t)}\,dW_t .$$

2. The number $A_t$ of ancestral lineages of a sample is a branching–coalescing Markov chain with generator

    $$Gh(n)=\binom n2\big[h(n-1)-h(n)\big]+\sigma n\sum_{k\ge1}\Big(\tfrac34\Big)^{k-1}\tfrac14\big[h(n+\eta(f,k)-1)-h(n)\big].$$

3. *(Duality.)* Let $\mathbf B_n(y)=\big(\binom ni y^i(1-y)^{n-i}\big)_{i=0}^n$ be the vector of Bernstein polynomials of degree $n$ and $\langle\mathbf u,\mathbf v\rangle=\sum_i u_iv_i$. Let $(\mathbf V_t)_{t\ge0}$ be the Markov jump process of Bernstein coefficient vectors whose transitions from a vector $\mathbf v=(v_0,\dots,v_m)$ of length $m+1$ are:

    - *(branching)* for each $k\ge1$, at rate $m\sigma(\tfrac34)^{k-1}\tfrac14$, with $\eta=\eta(f,k)$, the jump to the vector $\mathbf v'=(v'_0,\dots,v'_{m+\eta-1})$ given by

        $$v'_i=\sum_{j=0}^{i\wedge\eta}\frac{\binom ij\binom{m+\eta-1-i}{\eta-j}}{\binom{m+\eta-1}{\eta}}\Big[\mathbf 1\Big\{f_k\Big(\tfrac j\eta\Big)\ge\tfrac12\Big\}v_{i+1-j}+\mathbf 1\Big\{f_k\Big(\tfrac j\eta\Big)<\tfrac12\Big\}v_{i-j}\Big],$$

        with $v_l:=0$ for $l\notin\{0,\dots,m\}$; the weight is the hypergeometric probability that $j$ of the $\eta$ new ancestors carry $A$ when $i$ of the $m+\eta-1$ lineages do;
    - *(coalescence)* at rate $\binom m2$, the jump to $\mathbf v'=(v'_0,\dots,v'_{m-1})$ with $v'_i=\frac{i}{m-1}v_{i+1}+\frac{m-1-i}{m-1}v_i$.

    Then, with $Y$ the diffusion of item 1, for all $t\ge0$, every $y\in[0,1]$, every $n\in\mathbb N$ and every $\mathbf v\in\mathbb R^{n+1}$,

    $$\mathbb E\big[\langle\mathbf B_n(Y_t),\mathbf v\rangle\,\big|\,Y_0=y\big]=\mathbb E\big[\langle\mathbf B_{\dim(\mathbf V_t)-1}(y),\mathbf V_t\rangle\,\big|\,\mathbf V_0=\mathbf v\big].$$

    The dimension $\dim(\mathbf V_t)-1$ is the ancestral process $A_t$ of item 2 started from $A_0=n$. The source prints the hypergeometric weight in an equivalent arrangement.

4. *(Allen–Cahn.)* On a Lipschitz domain $\Omega\subseteq\mathbb R^d$, run a branching Brownian motion (speed $2$, so its generator is $\Delta$) reflected at $\partial\Omega$, started from one particle at $x$ and branching at rate $\lambda>0$ into $\eta(f,L)$ offspring with $L\sim\mathrm{Geo}(1/4)$. At time $t$ each leaf at $z$ independently carries allele $A$ with probability $u_0(z)$, and alleles propagate rootwards: a branch with $\eta(f,k)$ offspring, $j$ of them $A$, carries $A$ if $f_k(j/\eta(f,k))\ge\tfrac12$, so each branching event uses the Bernoulli factory as a voting rule and turns $u$-coins into an $f(u)$-coin. The probability $u(x,t)=\mathbb P(F(x,t)=A)$ that the root ends up with allele $A$ solves

    $$\partial_tu-\Delta u=\lambda\big(f(u)-u\big),\qquad \partial_nu=0\ \text{on }\partial\Omega,\qquad u(\cdot,0)=u_0.$$

The reaction is $\lambda(f(u)-u)$, not $\lambda f(u)$: at rate $\lambda$ a branching event replaces the current value $u$ by the factory output $f(u)$, so with the identity factory $f(u)=u$ and a constant initial frequency the solution stays constant. (The source displays the equation as $\partial_tu-\Delta u=\lambda f(u)$, but its proof derives $\lambda[f(u)-u]$.) This extends the voting construction for the Allen–Cahn nonlinearity $\varepsilon^{-2}u(1-u)(2u-1+\nu\varepsilon)$, which has this form $\lambda(f(u)-u)$ with $\lambda=(1+\nu\varepsilon)/\varepsilon^2$ and a cubic voting polynomial $f$, used in spatial models of hybrid zones, where an internal branch takes the majority vote of its three children with a small correction, to any continuous, polynomially bounded $f$.

## Proof depends on

- [Moment duality with Kingman's coalescent](../../wright-fisher-diffusion/generator-pow.md)

## Expansion

Classical [moment duality](../../wright-fisher-diffusion/generator-pow.md) matches $\mathbb E[Y_t^n]$ with a coalescent. For a general drift $\sigma(f(y)-y)$, the generator applied to $y^n$ gives $f(y)y^{n-1}$, which is not a polynomial unless $f$ is. Writing $f$ as a convergent mixture of Bernstein polynomials of degrees $\eta(f,k)$ with weights $(3/4)^{k-1}/4$ solves this. Each "selective" event replaces one lineage by $\eta(f,k)$ lineages, so the dual stays in the class of Bernstein-polynomial expectations, now with a type vector tracking which coin outcomes produce $A$. Any frequency-dependent selection, mutation or dominance scheme with such an $f$ therefore has an ancestral process made of coalescence and finite multi-branching. In spatial models, this gives a probabilistic, genealogical solution of reaction–diffusion equations with general reaction terms.

## Sources

- Jere Koskela, Krzysztof Łatuszyński and Dario Spanò, "Bernoulli factories and duality in Wright–Fisher and Allen–Cahn models of population genetics", *Theoretical Population Biology* 156 (2024), 40–45, <https://doi.org/10.1016/j.tpb.2024.01.002>. Numbering as in the preprint arXiv:2306.03539v3, <https://arxiv.org/abs/2306.03539v3>: Section 2 (Keane–O'Brien factory), Theorem 1 (diffusion limit), Theorem 2 (ancestral process), Theorem 3 (Bernstein duality), Section 4, equation (11) and Theorem 4 with its proof (Allen–Cahn representation).
