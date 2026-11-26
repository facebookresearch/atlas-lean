# Shared recombination endpoints in coalescent IBD simulation

Work at a focal position on a chromosome with crossovers forming a Poisson process along genetic distance (in Morgans) in each meiosis, in a population of constant haploid size scaled by $N$, with Kingman coalescent times measured in units of $N$ generations.

**Segment lengths.** If a lineage descends from an ancestor $Nt$ generations ago, the distance $R$ from the focal position to the first crossover on its right, and the length $W$ of the segment overlapping the focal position, satisfy

$$\Pr(R > w \mid t) = e^{-Ntw}, \qquad \Pr(W > w \mid t) = e^{-Ntw}\,(1 + Ntw), \qquad w \ge 0.$$

**Coalescent times.** With $n$ sampled haploids, the expected time until only $k-1$ lineages remain is

$$\mathbb E[T^+_{n:k}] = \sum_{l=k}^{n} \binom{l}{2}^{-1} = 2\Bigl(\frac{1}{k-1} - \frac1n\Bigr).$$

**Merging of endpoints.** Let haplotypes $a, b$ coalesce into ancestor $c$ at time $u$ and $c$ coalesce with another lineage into $e$ at time $u + v$. The right endpoints accumulated on the branches satisfy $R_{a,c}, R_{b,c} \sim \mathrm{Exp}(u)$ and $R_{c,e} \sim \mathrm{Exp}(v)$, independent. Then $a$ and $b$ carry the same endpoint above $c$ (the shared branch has the first crossover) with probability

$$\Pr\bigl(\min(R_{a,c}, R_{b,c}, R_{c,e}) = R_{c,e}\bigr) = \frac{v}{2u + v}.$$

Setting $u/2 = \mathbb E[T^+_{n:(k+1)}]$ and $v/2 = \mathbb E[T^+_{n:(j+1)}] - \mathbb E[T^+_{n:(k+1)}]$ with $j < k \le n$, this probability equals $\dfrac{1 - j/k}{1 + j/k - 2j/n} = \dfrac{(k-j)n}{nk + nj - 2kj}$, which equals $1$ at $j = 1$, $k = n$ (where $u = 0$) and tends to $1$ whenever $j = o(k)$: haplotypes joined by a recent ancestor almost surely share their endpoints at much older coalescences, so they can be merged into one comparison.

**Cost of deep coalescences.** If $B_0 = n$ and $B_j \sim \mathrm{Binomial}(B_{j-1}, 1/2)$ for a bounded index $j \ge 1$ (the subtree sizes under random halving), then $\mathbb E[B_j(B_{j-1} - B_j)] = n(n-1)\,2^{-2j}$ and

$$\lim_{n \to \infty} \frac{\mathbb E[B_j(B_{j-1} - B_j)] + O(1)\cdot \operatorname{Cov}^{1/2}\bigl(B_j(B_{j-1} - B_j)\bigr)}{n^2/2^{2j}} = 1,$$

so the number of pairwise endpoint comparisons at the oldest coalescences is, with high probability, of the same quadratic order as the worst case.

## Depends on

- [Holding times of Kingman's coalescent](../../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)

## Proof depends on

- [Expected coalescent holding time](../../kingman-s-coalescent-and-watterson-s-estimator/integral-t.md)
- [Sum of reciprocals of binomial coefficients $\binom{k}{2}$](../../kingman-s-coalescent-and-watterson-s-estimator/sum-inv-choose-two.md)

## Expansion

A lineage of age $Nt$ generations has experienced $Nt$ meioses, so crossovers to the right of the focal point arrive at rate $Nt$ per Morgan, giving the exponential tail of $R$; $W$ is the sum of two independent such exponentials (left and right), whose tail is the Gamma(2) formula. The minimum of independent exponentials with rates $u, u, v$ is the one of rate $v$ with probability $v/(2u+v)$; substituting twice the expected coalescent times gives a ratio $(1/j - 1/k)/(1/j + 1/k - 2/n)$ that tends to $1$ when $j/k \to 0$. For the cost bound, $\mathbb E[B(B-1)] = m(m-1)/4$ for $B \sim \mathrm{Binomial}(m, 1/2)$; iterating the law of total expectation gives the exact mean, and recursive application of the law of total covariance shows the standard deviation is $o(n^2)$, because the coefficient of variation of a $\mathrm{Binomial}(m,1/2)$ variable is of order $m^{-1/2}$. Together: comparisons concentrate at old coalescences, where segments are almost never long enough to be detected (so lineages can be pruned) and recent sister haplotypes share endpoints (so they can be merged), which is why such simulation runs in roughly linear time in practice.

## Sources

- S. D. Temple, S. R. Browning, E. A. Thompson, "Fast simulation of identity-by-descent segments", *Bulletin of Mathematical Biology* (2025), Sections on pruning, merging and the number of comparisons (Eqs. (6)–(8), Proposition 1, Theorem 1 with Eqs. (9)–(12)), <https://doi.org/10.1007/s11538-025-01464-8> (PMC12102126).
