# Read-length thresholds for metagenome identifiability

**Model.** A metagenomic sample consists of $M$ genomes $X^1,\dots,X^M\in\mathcal A^N$ over a finite alphabet $\mathcal A$, genome $m$ having i.i.d. symbols with law $p^m$. Shotgun sequencing gives the multiset $\mathcal R(X)$ of all length-$L$ substrings (reads) of all genomes. The collection is **identifiable** (event $I$) if no other collection of genomes, up to relabeling, has the same read multiset. For a law $p$ define the Rényi entropy of order two $H_2(p)=-\log\sum_ap(a)^2$ and, for two laws, $F(p,p')=-\log\sum_ap(a)p'(a)$ (so $F(p,p')\ge\tfrac12H_2(p)+\tfrac12H_2(p')$).

**Theorem (sufficient read length).** Consider a sequence of problems $(M_n,N_n,L_n,P_n)$ with $N_n\to\infty$ and $H_2(p_n^m)\ge H_*>0$ for all genomes. If for some $\epsilon>0$

$$L_n\ge\frac{2(1+\epsilon)}{H_*}\log(M_nN_n)$$

for all large $n$, then $\mathbb P(I_n)\to1$, and a simple greedy overlap algorithm reconstructs all genomes.

**Theorem (necessary read length).** Suppose $M_n\ge2$, $N_n\to\infty$, $\log(M_n)/N_n\to0$, there exist $F_*, F^* \in (0, \infty)$ such that $F_* \le F(p_n^m, p_n^{m'}) \le F^*$ for all $n$ and all pairs $1 \le m, m' \le M_n$, and $L_n\le\delta N_n$ for some $\delta<1$. With $C=\min\{1/F^*,\ 1/(2F^*-F_*)\}$, if for some $\epsilon>0$

$$L_n\le C(1-\epsilon)\log(M_nN_n)$$

for all large $n$, then $\mathbb P(I_n)\to0$.

So reliable metagenomic reconstruction needs reads of length of order $\log(MN)$: growing the number of genomes $M$ raises the threshold only logarithmically, like growing the genome length.

## Expansion

Ambiguity in reconstruction comes from long repeated substrings, within one genome or shared between genomes, that let pieces be reassembled in more than one way. The probability that two independent positions agree on a stretch of length $\ell$ decays like $e^{-\ell H_2}$ within a genome and like $e^{-\ell F}$ across genomes, and there are of order $(MN)^2$ position pairs, which is why both thresholds scale as $\log(MN)$ divided by these collision exponents. Above the upper threshold, long repeats are absent with high probability and greedy merging of maximal overlaps recovers each genome; below the lower threshold, repeat configurations that make two different collections share the same read multiset occur with probability tending to one.

## Sources

- Marlee Herring, "A probabilistic analysis of shotgun sequencing for metagenomics", arXiv:2201.05029 (2022), Section 2 (model, Theorems 1 and 2), <https://doi.org/10.48550/arXiv.2201.05029>.
