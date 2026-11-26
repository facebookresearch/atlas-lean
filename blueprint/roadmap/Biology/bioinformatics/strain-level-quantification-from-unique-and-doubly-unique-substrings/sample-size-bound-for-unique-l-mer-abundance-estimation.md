# Sample-size bound for unique-$L$-mer abundance estimation

Let a sample contain genomes $s_1,\dots,s_a$ with abundances $p_1,\dots,p_a > 0$, $\sum_i p_i = 1$, drawn from a reference collection. Let $n_i^L$ be the number of $L$-mers of $s_i$ and $q_i > 0$ the proportion of them that are unique (occur in no other reference genome). Suppose $n$ error-free reads of length $L$ are sampled independently, each by first picking genome $s_i$ and then a uniformly random start position on it, so that a read comes from $s_i$ with probability proportional to its share of $L$-mers. Write

$$p_i' = \frac{p_i\, n_i^L}{\sum_{i'=1}^a p_{i'}\, n_{i'}^L}$$

for the resulting unnormalized abundance, $c_i$ for the number of reads that contain a unique $L$-mer of $s_i$ (and are therefore assigned to $s_i$), $\hat p_i = c_i/(q_i n)$, $p_{\min} = \min_i p_i$ and $q_{\min} = \min_i q_i$. Then for every $\zeta \in (0,1)$:

1. with probability at least $1-\zeta$ every $s_i$ receives at least one read (is identified) if $n \ge 2\bigl((a+1) + \ln(1/\zeta)\bigr)/(p_{\min} q_{\min})^2$;
2. with probability at least $1-\zeta$, $\sum_i |\hat p_i - p_i'| \le \epsilon$ if $n \ge 2\bigl((a+1) + \ln(1/\zeta)\bigr)/(\epsilon\, q_{\min})^2$;
3. equivalently, for a given $n$, with probability at least $1-\zeta$, $\sum_i |\hat p_i - p_i'| \le \sqrt{2\bigl(\ln(1/\zeta) + (a+1)\bigr)/(n\, q_{\min}^2)}$.

## Expansion

Each read falls into one of $a+1$ categories: "contains a unique $L$-mer of $s_i$" for $i = 1,\dots,a$, with probability $p_i' q_i$, or "contains no unique $L$-mer". The counts $(c_1,\dots,c_a, n - \sum c_i)$ are multinomial, and the $L^1$ concentration inequality for empirical distributions on $a+1$ cells gives $\Pr\bigl(\sum_i |c_i/n - p_i' q_i| > \delta\bigr) \le 2^{a+1}e^{-n\delta^2/2} \le e^{(a+1) - n\delta^2/2}$. Dividing the $i$-th coordinate by $q_i \ge q_{\min}$ inflates the error by at most $1/q_{\min}$, which gives parts 2 and 3; part 1 follows by asking the error to be smaller than the smallest cell probability. The bound explains why a method that relies only on unique substrings degrades on closely related strains, where $q_{\min}$ is small, and motivates the use of doubly-unique substrings.

## Sources

- K. Zhu, A. A. Schäffer, W. Robinson, J. Xu, E. Ruppin, A. F. Ergun, Y. Ye and S. C. Sahinalp, "Strain level microbial detection and quantification with applications to single cell metagenomics", Nature Communications 13 (2022), 6430, <https://doi.org/10.1038/s41467-022-33869-7>, PMCID PMC9616933. Theorem 1 (proof in its Supplementary Note 4).
