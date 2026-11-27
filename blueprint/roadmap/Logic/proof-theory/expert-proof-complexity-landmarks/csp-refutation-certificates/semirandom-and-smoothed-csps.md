# Semirandom and smoothed CSP instances and strong refutation

A semirandom Boolean CSP has a worst-case collection of constraint scopes and uniformly random literal negations; a smoothed CSP starts from a worst-case instance and rerandomizes each literal independently with a small probability. A strong refutation algorithm certifies, for most such instances, that no assignment satisfies more than a $1-\delta$ fraction.

Let $P:\{\pm1\}^k\to\{0,1\}$ be a $k$-ary predicate. An instance $\phi$ of CSP($P$) on variables $x_1,\dots,x_n\in\{\pm1\}$ consists of a collection $\mathcal{H}$ of $m$ scopes $C=(C_1,\dots,C_k)$, each a $k$-tuple of variable indices with $C_i\neq C_j$ for $i\neq j$, and literal negation patterns $\Xi(C)\in\{\pm1\}^k$, one for each $C\in\mathcal{H}$; the constraint for $C$ is

$$
P(\Xi(C)_1x_{C_1},\Xi(C)_2x_{C_2},\dots,\Xi(C)_kx_{C_k})=1 .
$$

The value $\mathrm{val}(\phi)$ is the maximum, over $x\in\{\pm1\}^n$, of the fraction of the $m$ constraints that $x$ satisfies.

- In a **fully random** instance, $\mathcal{H}$ consists of $m$ independent uniformly random $k$-tuples and the patterns $\Xi(C)$ are independent and uniform on $\{\pm1\}^k$.
- In a **semirandom** instance, $\mathcal{H}$ is arbitrary (worst case) and the patterns $\Xi(C)$ are independent and uniform on $\{\pm1\}^k$.
- In a **smoothed** instance, start from an arbitrary instance $\psi=(\mathcal{H},\Xi)$ and smoothing parameters $p_{C,i}\in[0,1]$ for $C\in\mathcal{H}$, $i\in[k]$. The $\vec{p}$-smoothing $\psi_s$ of $\psi$ is obtained by choosing, independently for each $C$, a set $S_C\subseteq[k]$ that contains each $i$ independently with probability $p_{C,i}$, and resetting $\Xi(C)_i$ to an independent uniform bit in $\{\pm1\}$ for every $i\in S_C$. Equivalently, each $\Xi(C)_i$ is flipped independently with probability $p_{C,i}/2$. Taking all $p_{C,i}=1$ gives the semirandom model; the introductory model of the source flips each literal with probability $0.01$.

A **refutation algorithm** takes an instance $\phi$ and outputs $\mathrm{algval}(\phi)\in[0,1]$ with $\mathrm{algval}(\phi)\ge\mathrm{val}(\phi)$ for every $\phi$. For a distribution $\mathcal{D}$ on instances it **weakly refutes** $\mathcal{D}$ if $\mathrm{algval}(\phi)<1$ with high probability over $\phi\sim\mathcal{D}$, **strongly refutes** $\mathcal{D}$ if $\mathrm{algval}(\phi)<1-\delta$ with high probability for some absolute constant $\delta>0$, and **$\epsilon$-tightly refutes** $\mathcal{D}$ if $\mathrm{algval}(\phi)<\mathrm{val}(\phi)+\epsilon$ with high probability, where $\epsilon>0$ is a parameter that can be made arbitrarily small.

Two further notions govern the number of constraints these algorithms need.

- A distribution $\mu$ on $\{\pm1\}^k$ is **$t$-wise uniform** if $\mathbb{E}_{z\sim\mu}\prod_{i\in S}z_i=0$ for every nonempty $S\subseteq[k]$ with $|S|\le t$. The **degree of uniformity** $t(P)\le k$ is the smallest $t$ such that no $t$-wise uniform distribution is supported on $P^{-1}(1)$. For $k$-SAT, $t(P)=k$, since the uniform distribution on odd-parity strings is $(k-1)$-wise uniform and supported on satisfying assignments.
- A **degree-$d$ pseudo-expectation over $\{\pm1\}^n$** is a linear map $\tilde{\mathbb{E}}$ from polynomials of degree at most $d$ to $\mathbb{R}$ with $\tilde{\mathbb{E}}[1]=1$, $\tilde{\mathbb{E}}[fx_i^2]=\tilde{\mathbb{E}}[f]$ for every $i$ and every $f$ of degree at most $d-2$, and $\tilde{\mathbb{E}}[f^2]\ge0$ for every $f$ of degree at most $d/2$. The **canonical degree-$d$ sum-of-squares relaxation** of a CSP maximizes $\tilde{\mathbb{E}}$ of the polynomial counting satisfied constraints over all such $\tilde{\mathbb{E}}$; its value upper-bounds $\mathrm{val}$, since the expectation over any distribution on $\{\pm1\}^n$ is a pseudo-expectation of every degree, and it can be computed to within $2^{-n}$ in time $n^{O(d)}$.

## Expansion

The models are nested: every fully random instance is semirandom in distribution, and every semirandom instance is a smoothed instance with all $p_{C,i}=1$. In the semirandom and smoothed models the scopes can be chosen adversarially, so algorithms that rely on the random structure of $\mathcal{H}$ (trace moment computations over random hypergraphs) no longer apply. A refutation algorithm whose output is the value of a degree-$d$ sum-of-squares relaxation yields, on each instance it refutes, a dual certificate: a degree-$d$ sum-of-squares proof that the satisfied-constraint polynomial is at most $\mathrm{algval}(\phi)$ on the hypercube. Feige formalized the semirandom and smoothed CSP models; for resolution, random CNFs with linearly many clauses already need exponential-size refutations ([random $k$-CNF lower bound](../../../proof-theory/resolution-separations-and-supercritical-tradeoffs/chvatal-szemeredi-random.md)), whereas the algorithms here work at polynomially many more constraints and produce semidefinite certificates.

## Depends on

None.

## Proof depends on

None.

## Sources

- Venkatesan Guruswami, Pravesh K. Kothari, Peter Manohar, "Algorithms and Certificates for Boolean CSP Refutation: Smoothed is no harder than Random", *STOC 2022*, 2022, arXiv:2109.04415v2, https://arxiv.org/abs/2109.04415 (Definitions 1.1 and 1.2, Definition 3.3, Fact 3.4, Definition 7.1, Remark 7.2, Definition 7.3).
- Jackson Abascal, Venkatesan Guruswami, Pravesh K. Kothari, "Strongly refuting all semi-random Boolean CSPs", *SODA 2021*, 2021, arXiv:2009.08032v1, https://arxiv.org/abs/2009.08032 (Section 1, semi-random model and weak versus strong refutation; Section 3, semi-random $k$-XOR instances).
