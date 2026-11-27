# Uniform-coverage integer program for abundance with doubly-unique substrings

Let $S = \{s_1,\dots,s_m\}$ be reference genomes and $L$ the read length. A substring of $s_i$ is *unique* if it occurs in no other genome and *doubly-unique* if it occurs in exactly one other genome $s_j$; a *shortest* one contains no proper substring with the same property. For each genome keep a set of $n_{u_i}$ shortest unique substrings $u_{i,l}$ and $n_{d_i}$ shortest doubly-unique substrings $d_{i,l}$ (with partner genome $j = j(i,l)$), and let $c(\cdot)$ count the conflict-free reads of the query that contain each indexed substring. With presence indicators $\delta_i \in \{0,1\}$, abundances $p_i \ge 0$ and an estimated per-base substitution error rate $\widehat{\mathrm{err}}$, the abundances solve

$$\min \sum_i \Bigl(\frac{1}{n_{u_i}}\sum_{l=1}^{n_{u_i}} |c(u_{i,l}) - e(u_{i,l})| + \frac{1}{n_{d_i}}\sum_{l=1}^{n_{d_i}} |c(d_{i,l}) - e(d_{i,l})|\Bigr)$$

subject to

$$e(u_{i,l}) = \frac{L - |u_{i,l}| + 1}{L}\, p_i\, (1-\widehat{\mathrm{err}})^{|u_{i,l}|}, \qquad e(d_{i,l}) = \frac{L - |d_{i,l}| + 1}{L}\,(p_i + p_j)\,(1-\widehat{\mathrm{err}})^{|d_{i,l}|},$$

$p_i \le \delta_i p_{\max}$, $\delta_i = 0$ for genomes whose unique and doubly-unique counts both fall below a noise threshold, a lower bound on $p_i$ for $\delta_i = 1$ tied to the observed coverage of its indexed substrings, and the read budget $\sum_i |s_i|\, p_i \le nL$. The absolute values are linearized by auxiliary variables $\gamma \ge \pm(c - e)$, giving a mixed integer linear program. The expected counts encode the assumption that coverage is uniform along each genome: a substring of length $\ell \le L$ lies inside $L - \ell + 1$ of the $L$ read placements covering a position, and is error free with probability $(1-\widehat{\mathrm{err}})^{\ell}$ under independent substitutions.

Dropping the coverage terms and asking only for the smallest set of genomes that contains every unique and doubly-unique substring seen in the reads is a hitting-set problem whose sets have at most two elements; it is NP-hard because it contains vertex cover.

## Depends on

- [Sample-size bound for unique-$L$-mer abundance estimation](sample-size-bound-for-unique-l-mer-abundance-estimation.md)

## Proof depends on

- [VERTEX-COVER (exact size $k$) is NP-hard](../../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/clique-independent-set-and-vertex-cover/part-08/vertex-cover-dec-np-hard.md)

## Expansion

A read from genome $s_i$ contains a fixed length-$\ell$ substring of $s_i$ when its start lies in a window of $L-\ell+1$ positions, which gives the coverage factor. Doubly-unique substrings let a genome without any unique substrings be detected, because its share of a shared substring's coverage must make the coverage of both partner genomes uniform at the same time. The paper also chooses the maximum indexed length $L/2$ by maximizing the product of substring length fraction $1 - 1/\Delta$ and coverage fraction $1/\Delta$, which peaks at $\Delta = 2$.

## Sources

- K. Zhu, A. A. Schäffer, W. Robinson, J. Xu, E. Ruppin, A. F. Ergun, Y. Ye and S. C. Sahinalp, "Strain level microbial detection and quantification with applications to single cell metagenomics", Nature Communications 13 (2022), 6430, <https://doi.org/10.1038/s41467-022-33869-7>, PMCID PMC9616933. Methods, query processing stage 2 (constraints (1)–(6)) and the discussion of query types $A_2$ and $A_3$.
