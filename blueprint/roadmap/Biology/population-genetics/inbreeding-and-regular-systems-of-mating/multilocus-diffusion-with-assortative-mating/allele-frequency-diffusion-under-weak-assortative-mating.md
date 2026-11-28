# Allele-frequency diffusion and stationary density under weak assortative mating

**Model.** A haploid population of size $N$ has types $\mathbf k \in \mathcal A = \{0,1\}^n$ ($n$ diallelic loci). In each step a first parent of type $\mathbf i$ is chosen with probability equal to its frequency, a second parent of type $\mathbf j$ with probability proportional to $(1 + s_{\mathbf i,\mathbf j}/N)$ times its frequency (assortative mating), and the first parent is replaced by an offspring that takes the loci in $L$ from the first parent and the others from the second with probability $r_L$, followed by mutation $1 \to 0$ with probability $\mu_1/N$ and $0 \to 1$ with probability $\mu_0/N$ at each locus. Assume: $r_L = r_{\bar L}$; the $r_L$ do not depend on $N$ and every pair of loci can be separated by recombination (loose linkage); $s_{\mathbf i,\mathbf j} = s_{\mathbf j,\mathbf i}$ depends only on the sets of loci where the two types differ in each direction. For $L \subseteq \{1,\dots,n\}$ let $F_L$ be the set of pairs of types that differ exactly on $L$ and

$$ m_L(s) = 2^{-n}\sum_{(\mathbf i,\mathbf j) \in F_L} s_{\mathbf i,\mathbf j} $$

the *mean assortment parameter* of $L$. Let $X^{(N)}_t \in [0,1]^n$ be the vector of frequencies of allele $0$ at the $n$ loci.

**Theorem (diffusion limit).** If $X^{(N)}_0$ converges in law, then $(X^{(N)}_{\lfloor N^2 t\rfloor})_{t \ge 0}$ converges in law in the Skorokhod space to the diffusion with generator

$$ \mathcal G_{n,s} = \frac12\sum_{i=1}^n x_i(1-x_i)\frac{\partial^2}{\partial x_i^2} + \sum_{i=1}^n\Big((1-x_i)\mu_1 - x_i\mu_0 + \big(\tfrac12 - x_i\big)x_i(1-x_i)P_{i,s}(x)\Big)\frac{\partial}{\partial x_i}, $$

$$ P_{i,s}(x) = \sum_{A \subseteq \{1,\dots,n\}\setminus\{i\}}\big(m_{A\cup\{i\}}(s) - m_A(s)\big)\prod_{k\in A}2x_k(1-x_k)\prod_{\ell \notin A\cup\{i\}}\big(1 - 2x_\ell(1-x_\ell)\big), $$

while linkage disequilibria vanish on the faster time scale $N$ (genotype frequencies become products of allele frequencies). The coordinates are independent one-locus diffusions iff $m_{L\cup\{i\}}(s) - m_L(s)$ does not depend on $L \subseteq \{1,\dots,n\}\setminus\{i\}$ for every $i$.

**Theorem (stationary density and boundaries).** If $\mu_0, \mu_1 > 0$, the diffusion has a unique stationary distribution, which is reversible, with density on $[0,1]^n$

$$ g_{n,\mu,s}(x) = C_{n,\mu,s}\prod_{i=1}^n x_i^{2\mu_1-1}(1-x_i)^{2\mu_0-1}\exp\big(H_{n,s}(x)\big), $$

$$ H_{n,s}(x) = \frac12\sum_{L \ne \varnothing} m_L(\tilde s)\prod_{\ell\in L}2x_\ell(1-x_\ell)\prod_{k \notin L}\big(1 - 2x_k(1-x_k)\big), \qquad \tilde s_{\mathbf i,\mathbf j} = s_{\mathbf i,\mathbf j} - s_{\mathbf 1,\mathbf 1}. $$

For each coordinate, $0$ is reached in finite time almost surely if $\mu_1 = 0 < \mu_0$, is attainable with positive probability if $0 < \mu_1 < \tfrac12$, and is inaccessible if $\mu_1 \ge \tfrac12$ (symmetrically for $1$ with $\mu_0$); with $\mu_0 = \mu_1 = 0$ the process leaves $(0,1)^n$ in finite time almost surely.

## Expansion

The proof uses the Ethier–Nagylaki theorem for Markov chains with a slow component (allele frequencies, changing by $O(N^{-1})$ per step with drift and variance of order $N^{-2}$) and a fast component (the linkage-disequilibrium coordinates $y(I) = \prod_{\ell\in I}x(\ell) - x(I)$, contracted by recombination at rate of order $N^{-1}$). Loose linkage makes the fast system $\dot v = c_{n,I}(x, v)$ converge exponentially to $0$, so in the limit genotype frequencies are products of allele frequencies, and averaging the selection-like term created by assortative mating over the product measure produces the polynomial $P_{i,s}$, rewritten in terms of the $m_L$ through Möbius-type inversion identities for functions on subsets. Since the diffusion matrix is diagonal with entries $x_i(1-x_i)$ and the selection-like part of the $i$-th drift equals $\frac12 x_i(1-x_i)\,\partial_{x_i}H_{n,s}$, the generator is symmetric with respect to $g_{n,\mu,s}$, which gives reversibility and the explicit Gibbs-type density. Boundary behaviour follows from Feller's test applied to each coordinate, whose drift near $0$ is dominated by $\mu_1$.

## Sources

- Alison M. Etheridge, Sophie Lemaire, "Diffusion approximation of a multilocus model with assortative mating", *Electronic Journal of Probability* 16 (2011), <https://doi.org/10.1214/EJP.v16-932>; preprint arXiv:1101.5485, <https://doi.org/10.48550/arXiv.1101.5485>. Numbering of the arXiv version: Section 2 (model and hypotheses), Section 4 (mean assortment parameters, Theorem 4.1), Section 5 (Lemma 5.1, Propositions 5.1–5.2), Section 6 (Propositions 6.1–6.3), Section 7 (Ethier–Nagylaki theorem, Lemmas 7.1–7.9).
