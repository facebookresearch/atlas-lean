# Entropy rate bounds for the multitype Moran process with mutation

**Model (incentive process).** A population of size $N > n$ consists of $a_i$ individuals of type $A_i$, $i = 1,\dots,n$, with state $a = (a_1,\dots,a_n)$ and $\bar a = a/N$. Let $\varphi(\bar a) = (\varphi_1(\bar a),\dots,\varphi_n(\bar a))$ be a nonnegative *incentive* (for the Moran process, $\varphi_i(\bar a) = \bar a_i f_i(\bar a)$ with fitness $f$) and $M$ a mutation matrix. At each step an individual reproduces with type-$i$ offspring probability

$$p_i(\bar a) = \frac{\sum_{k}\varphi_k(\bar a)\,M_{ik}}{\sum_k \varphi_k(\bar a)},$$

and a uniformly chosen individual is replaced, so $a \to a + e_j - e_k$ ($j \ne k$) with probability $T_a^{a+e_j-e_k} = p_j(\bar a)\,\bar a_k$, and otherwise the state is unchanged. Assume the chain has a stationary distribution $s$. Its **entropy rate** is $H(P) = \sum_a s_a H(T_a)$, where $H(T_a) = -\sum_b T_a^b\log T_a^b$ is the transition entropy at $a$.

**Theorem.**

1. (Universal bound.) For every incentive and every mutation matrix,

$$H(P) \le \frac{2n-1}{n}\,\log n.$$

This is the maximal entropy of a law on $n(n-1) + 1$ outcomes of the form $z_{jk} = x_jy_k$ ($j\ne k$), $z_0 = 1 - \sum_{j\ne k}z_{jk}$, with $x, y$ probability vectors, attained at $x = y = (1/n,\dots,1/n)$. If $n \mid N$, the transition entropy is maximal at the central state $(N/n,\dots,N/n)$.
2. (Neutral landscape.) With $M_{ij} = \mu/(n-1)$ for $i\ne j$, $M_{ii} = 1-\mu$, and neutral fitness, the stationary law is Dirichlet-multinomial, $s_a = \binom{N}{a}\prod_i(\alpha)_{a_i}/(n\alpha)_N$ with $\alpha = N\mu/(n-1-n\mu)$ ($\mu \ne (n-1)/n$); the entropy rate is increasing in $\mu$ for fixed $n, N$, and for fixed $\mu$ it tends to the maximum,

$$\lim_{N\to\infty} H(P) = \frac{2n-1}{n}\,\log n.$$

3. (Rare mutation.) For fixed $n$ and $N$, with $q$-replicator or $q$-Fermi incentives ($q \ge 1$) on linear fitness landscapes, $H(P) \to 0$ as $\mu\to0$.
4. (Comparison with transition entropies.) If $s_a > 0$ at some interior state then $H(P) > 0$; if $s$ has a global maximum (minimum) at $a$, then $H(P) \le H(T_a)$ ($\ge H(T_a)$).

## Depends on

- [Fixation probability of the Moran process](../moran-model/moran-fixation.md)

## Expansion

At any state the transition law has the product form $z_{jk} = p_j\,\bar a_k$ off the diagonal, so its entropy is at most that of the best product of two probability vectors; maximizing $-\sum_{j\ne k}x_jy_k\log(x_jy_k) - z_0\log z_0$ gives uniform $x = y$ and the value $\tfrac{2n-1}{n}\log n$. Averaging over $s$ preserves the bound. For the neutral landscape, as $N\to\infty$ with $\mu$ fixed, $\alpha\to\infty$ and the Dirichlet-multinomial law concentrates at the center, where both the incentive distribution and the type distribution are uniform, so the bound is attained in the limit. As $\mu\to0$ the stationary law concentrates on the absorbing vertices of the mutation-free process, where the chain almost surely stays put and the transition entropy is $0$.

## Sources

- Marc Harper, "Entropy rates of the multidimensional Moran processes and generalizations", arXiv (2014). Section 2 (incentive process, Dirichlet-multinomial stationary law, entropy rate), Proposition 1, Theorems 1–4, Corollaries 2–3. <https://doi.org/10.48550/arXiv.1401.2713>
