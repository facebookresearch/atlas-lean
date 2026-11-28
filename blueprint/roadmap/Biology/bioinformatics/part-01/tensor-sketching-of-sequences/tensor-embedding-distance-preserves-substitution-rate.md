# Tensor embedding distance preserves substitution rate

**Setting.** Let $\Sigma$ be a finite alphabet and $t\ge1$ a fixed subsequence length. The *tensor embedding* of a sequence $a\in\Sigma^n$ is the vector $T_a\in\mathbb Z_{\ge0}^{\Sigma^t}$ whose entry at $s=s_1\cdots s_t$ counts the index tuples $1\le i_1<\dots<i_t\le n$ with $a_{i_1}\cdots a_{i_t}=s$, i.e. the number of occurrences of $s$ as a (gapped) subsequence of $a$. The normalized tensor embedding distance is

$$d_{te}(a,b)=\binom{n}{2t-1}^{-1}\,\|T_a-T_b\|_2^2 .$$

**Lemma 1 (linear preservation of the mutation rate).** Let $a$ be uniform on $\Sigma^n$ and, for $r\in[0,1]$, let $b$ be obtained from $a$ by independently replacing each $a_i$, with probability $r$, by a character drawn uniformly from $\Sigma\setminus\{a_i\}$ (substitutions only). Then, for fixed $t$ and $n\to\infty$,

$$\mathbb E_{a,b}\big[d_{te}(a,b)\big]=(1+o(1))\cdot 2^{2t-1}\cdot|\Sigma|^{-t+1}\cdot r .$$

The expected embedding distance is thus linear in the per-site substitution rate (the normalized edit distance in this regime), with a constant that does not depend on the sequences.

## Expansion

Write $\|T_a-T_b\|_2^2=\sum_{s}(\sum_I(\mathbf 1[a_I=s]-\mathbf 1[b_I=s]))^2$ as a double sum over pairs of index sets $I,J$ of size $t$. Pairs with $|I\cup J|=2t$ are independent and contribute zero in expectation; the leading contribution comes from pairs sharing exactly one position, of which there are order $\binom{n}{2t-1}$, and each contributes a term proportional to the probability that a substitution hits the shared or another included position, giving a factor linear in $r$. The tensor *sketch* is a randomized projection of $T_a$ to dimension $D$, computable in $O(nt)$ time per sequence, whose squared distance is an unbiased estimate of the embedding distance; it is used to index long inexact seeds for sequence-to-graph alignment in a nearest-neighbor structure.

## Sources

- Joudaki A, Meterez A, Mustafa H, Groot Koerkamp R, Kahles A, Rätsch G, "Aligning distant sequences to graphs using long seed sketches", Genome Res 2023 Jul;33(7):1208-1217, Equations (1)-(2) and Lemma 1, <https://doi.org/10.1101/gr.277659.123>, PMCID PMC10538362.
