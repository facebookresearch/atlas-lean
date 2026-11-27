# External branches of the Bolthausen–Sznitman coalescent

**Setting.** The Bolthausen–Sznitman coalescent is the $\Lambda$-coalescent with $\Lambda$ the uniform distribution on $[0,1]$. For a sample of size $n$ let $\tau_{n,1}, \dots, \tau_{n,n}$ be the external branch lengths, $\mu_n(k) = \mathbb E[\tau_{n,1}^{k_1}\cdots\tau_{n,j}^{k_j}]$ for $k \in \mathbb N_0^j$, and $L_n^{\mathrm{ext}} = \sum_{i=1}^n \tau_{n,i}$ the total external branch length.

**Theorem.**

1. *(Joint moments.)* For every $j \in \mathbb N$ and $k = (k_1, \dots, k_j) \in \mathbb N_0^j$,

$$ \mu_n(k) \sim \frac{k_1!\cdots k_j!}{(\log n)^{k_1 + \cdots + k_j}}, \qquad n \to \infty. $$

2. *(Weak limit.)* $(\log n)\,(\tau_{n,1}, \dots, \tau_{n,n}, 0, 0, \dots) \to (\tau_1, \tau_2, \dots)$ in distribution, where the $\tau_i$ are independent standard exponential random variables.
3. *(Total external length.)* For each $k \in \mathbb N$, $\mathbb E[(L_n^{\mathrm{ext}})^k] \sim n^k/(\log n)^k$; in particular $\frac{\log n}{n}L_n^{\mathrm{ext}} \to 1$ in probability.
4. *(Exact covariance input.)* For $n \ge 2$,

$$ \mathbb E[\tau_{n,1}\tau_{n,2}] = \frac{2}{(n-1)!}\sum_{k=1}^{n-1}\frac{2^k - 1}{k^2}\, s(n-2, k-1), $$

   with $s(\cdot,\cdot)$ the absolute Stirling numbers of the first kind. Two external branches of the Bolthausen–Sznitman coalescent are positively correlated for every $n \ge 2$, whereas under Kingman's coalescent they are negatively correlated for every $n \ge 4$.

## Depends on

- [Recursion for joint moments of external branch lengths](recursion-for-joint-moments-of-external-branch-lengths.md)

## Expansion

For $\Lambda$ uniform the jump rates are $g_{nm} = \frac{n}{(n-m)(n-m+1)}$ and $g_n = n-1$, so the general recursion becomes explicit. Encoding the moments in the generating functions $f_k(z) = \sum_{n \ge j}\mu_n(k)z^{n-1}$ turns the recursion into the linear differential equation $\frac{d}{dz}\big(L(z)^{j-1}f_k^{(j-1)}(z)\big) = \frac{L(z)^{j-2}}{1-z}g_k(z)$ on the unit disc, with $L(z) = -\log(1-z)$, $g_1(z) = z/(1-z)$ and $g_k = \sum_i k_i f_{k-e_i}^{(j-1)}$, solved by a single integral; singularity analysis at $z = 1$ then yields the $(\log n)^{-|k|}$ asymptotics, the exact Stirling-number formula, and, since the limiting moments $k_1!\cdots k_j!$ are those of independent exponentials and determine their law, the weak limit. The total length follows by summing the joint moments over the $n^k$ choices of branches. The positive correlation reflects that a large merger tends to cut many external branches at the same time.

## Sources

- Jean-Stéphane Dhersin, Martin Möhle, "On the external branches of coalescents with multiple collisions", *Electronic Journal of Probability* 18 (2013), <https://doi.org/10.1214/EJP.v18-2286>; preprint arXiv:1209.3380, <https://doi.org/10.48550/arXiv.1209.3380>. Numbering of the arXiv version: Section 1 (Theorem 1.2, Corollaries 1.3–1.4), Section 3 (Lemma 3.1, Corollary 3.2), Section 4 (proofs).
