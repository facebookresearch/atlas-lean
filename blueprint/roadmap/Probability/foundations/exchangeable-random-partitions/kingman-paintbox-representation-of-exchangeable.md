# Kingman's paintbox representation of exchangeable random partitions

A random partition $\Pi$ of $\mathbb N=\{1,2,\dots\}$ is exchangeable if its law is invariant under every permutation of $\mathbb N$ with finite support; equivalently, its restrictions $\Pi_n$ to $[n]=\{1,\dots,n\}$ form a consistent family of exchangeable random partitions of $[n]$. A mass partition is a sequence $s=(s_1,s_2,\dots)$ with $s_1\ge s_2\ge\dots\ge0$ and $\sum_is_i\le1$. The paintbox partition $\rho_s$ is the law of the random partition obtained from iid uniform variables $U_1,U_2,\dots$ on $[0,1]$ and the intervals $I_k=[\sum_{i<k}s_i,\ \sum_{i\le k}s_i)$, by declaring $m\ne n$ in the same block if and only if $U_m$ and $U_n$ lie in the same $I_k$; integers with $U_m\ge\sum_is_i$ are singletons. Thus each integer joins block $k$ with probability $s_k$ and is a singleton with probability $1-\sum_is_i$.

**Theorem (Kingman).** Let $\Pi$ be an exchangeable random partition of $\mathbb N$. Then almost surely every block $B$ of $\Pi$ has an asymptotic frequency

$$\operatorname{freq}(B)=\lim_{n\to\infty}\frac{|B\cap[n]|}{n},$$

and if $S$ denotes the decreasing rearrangement of the frequencies of the blocks (a random mass partition, with singletons contributing frequency $0$), then conditionally on $S=s$ the partition $\Pi$ has law $\rho_s$. Hence the law of $\Pi$ is the mixture $\int\rho_s\,\nu(ds)$, where $\nu$ is the law of $S$, and the total frequency of singletons is $1-\sum_iS_i$.

## Proof depends on

- [De Finetti theorem for exchangeable sequences in a standard Borel space](../exchangeable-sequences/de-finetti-theorem-for-exchangeable-sequences-in.md)
- Finite set partitions and the [multinomial distribution](../../distributions/discrete/multinomial-distribution/multinomial.md)

## Expansion

A full proof labels each integer by the smallest element of its block, applies [de Finetti's theorem](../exchangeable-sequences/de-finetti-theorem-for-exchangeable-sequences-in.md) to an exchangeable sequence constructed from $\Pi$ and independent uniform labels, reads off the directing measure's atoms as the block frequencies, and identifies the conditional law with the paintbox. It should also show that the Ewens partition with parameter $\theta>0$ corresponds to the Poisson–Dirichlet($\theta$) mass partition.

## Sources

- O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021, <https://link.springer.com/book/10.1007/978-3-030-61871-1>, exchangeable partitions (topic).
