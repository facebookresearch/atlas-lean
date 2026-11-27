# Subsampling lemma for column union cardinalities

**Lemma 1 (subsampling lemma).** Let $o_1, \dots, o_m \subset \{1, \dots, n\}$ with minimum cardinality $d = \min_i |o_i| > 0$. Sample each element of $\{1, \dots, n\}$ independently with probability $p$ into a set $S$, put $\tilde{o}_i = o_i \cap S$, and estimate the union cardinalities $u_{ij} = |o_i \cup o_j|$ by

$$\hat{u}_{ij} = \frac{1}{p} \, |\tilde{o}_i \cup \tilde{o}_j|.$$

Then for all $0 < \varepsilon < 1$ and $0 < \delta < 1$, if

$$p \ge \min\left\{ \frac{3 \ln\big((m^2 + m)/\delta\big)}{d \, \varepsilon^2}, \ 1 \right\},$$

it holds that

$$\Pr\Big( \bigcap_{i,j=1}^{m} \big\{ |\hat{u}_{ij} - u_{ij}| < \varepsilon \, u_{ij} \big\} \Big) \ge 1 - \delta.$$

In the annotation setting the $o_i$ are the object sets of the label columns, and the lemma justifies estimating all pairwise column similarities used for greedy column matching from a random subset of about $3 n \ln((m^2 + m)/\delta)/(d \varepsilon^2)$ rows instead of all $n$ rows, reducing the $O(n m^2)$ cost of exact computation.

## Depends on

- [Multi-BRWT representation of a genome graph annotation](multi-brwt-representation-and-node-removal-cost.md)

## Expansion

For a fixed pair, $|\tilde{o}_i \cup \tilde{o}_j|$ is a sum of $u_{ij}$ independent Bernoulli($p$) variables with mean $p u_{ij} \ge p d$. A multiplicative Chernoff bound gives $\Pr(|\hat{u}_{ij} - u_{ij}| \ge \varepsilon u_{ij}) \le 2 \exp(-p u_{ij} \varepsilon^2 / 3) \le 2\exp(-p d \varepsilon^2/3)$, and a union bound over the at most $(m^2 + m)/2$ unordered pairs (including $i = j$) gives total failure probability at most $(m^2 + m)\exp(-p d \varepsilon^2 / 3)$, which is at most $\delta$ under the stated condition on $p$; the case $p = 1$ is exact.

## Sources

- M. Karasikov, H. Mustafa, A. Joudaki, S. Javadzadeh-No, G. Rätsch, A. Kahles, "Sparse binary relation representations for genome graph annotation", Journal of Computational Biology 27(4) (2020) 626-639, Sections 2.2.5 and 2.3 (Equations 2-5, Lemma 1), <https://doi.org/10.1089/cmb.2019.0324> (PMC7185347).
