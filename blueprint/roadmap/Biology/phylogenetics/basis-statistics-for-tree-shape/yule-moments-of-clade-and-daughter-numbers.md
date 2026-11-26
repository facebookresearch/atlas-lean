# Yule moments of clade numbers and daughter numbers

Let $T$ be a random rooted binary tree with $n$ leaves under the Yule (equal-rates Markov) model. Let $C_r(T)$ be the number of clades of size $r$ and $D_{i,j}(T)$ the number of inner vertices with daughter clades of sizes $i\le j$. Write $p_r(i)=2/(r-1)$ if $1\le i<r/2$ and $p_r(r/2)=1/(r-1)$ for the Yule probability that a clade of size $r$ splits as $(i,r-i)$.

Clade numbers. For $2\le r\le n-1$, $M(n,r):=\mathbb{E}[C_r]=\frac{2n}{r(r+1)}$ and $M(n,n)=1$;

$$V(n,r):=\mathrm{Var}[C_r]=\begin{cases}\dfrac{2(4r^2-3r-4)(r-1)n}{r(r+1)^2(2r-1)(2r+1)}, & r<\tfrac n2,\\[1.2ex] \dfrac{(5r-7)(r-1)n}{r(r+1)^2(2r-1)}, & r=\tfrac n2,\\[1.2ex] \dfrac{2(r^2+r-2n)n}{r^2(r+1)^2}, & \tfrac n2<r\le n-1,\end{cases}$$

and $V(n,n)=0$. For $2\le r<s\le n-1$,

$$\mathrm{Cov}[C_r,C_s]=\begin{cases}-\dfrac{4n(r-1)(r+2s)}{s(s+1)(r+s)(r+s+1)(r+s-1)}, & r+s<n,\\[1.2ex] -\dfrac{2(r-1)\big(2r-s(s-3)\big)}{(r+1)s(s+1)(r+s-1)}, & r+s=n,\\[1.2ex] \dfrac{4n(s-n)}{r(r+1)s(s+1)}, & r+s>n,\end{cases}$$

and $\mathrm{Cov}[C_r,C_n]=0$.

Daughter numbers. With $r=i+j$ and $s=k+\ell$:

- $\mathbb{E}[D_{i,j}]=p_r(i)\,M(n,r)$ and $\mathrm{Var}[D_{i,j}]=p_r(i)(1-p_r(i))M(n,r)+p_r(i)^2V(n,r)$;
- if $r=s$ and $i\ne k$, $\mathrm{Cov}[D_{i,j},D_{k,\ell}]=p_r(i)p_r(k)\,[V(n,r)-M(n,r)]$;
- if $r<s$, $\mathrm{Cov}[D_{i,j},D_{k,\ell}]=p_r(i)p_s(k)\big[\mathrm{Cov}[C_r,C_s]+M(n,s)\big(\mathbf{1}_{\{k\ge r\}}M(k,r)+\mathbf{1}_{\{\ell\ge r\}}M(\ell,r)-M(s,r)\big)\big]$.

Consequences: combined with basis representations these give exact Yule means, variances and covariances of every balance index represented by the clade-number or daughter-number basis; for instance $\mathbb{E}[S(T)]=2n(H_n-1)$ for the Sackin index, with $H_n$ the $n$-th harmonic number, and $\mathbb{E}[\hat s(T)]=\log(n-1)+2n\sum_{r=2}^{n-1}\frac{\log(r-1)}{r(r+1)}$ for the $\hat s$-shape statistic.

## Expansion

Write $C_r=\sum_{|A|=r}Z_A$ over leaf subsets $A$, with $Z_A$ the indicator that $A$ is a clade. Yule probabilities that one or two given subsets are clades are known in closed form; summing them over pairs of subsets of sizes $r,s$ by their nesting or disjointness gives the second moments. Given that $A$ is a clade, its subtree is itself a Yule tree on $|A|$ leaves (group elimination), so the root split of the clade is independent of the outside and has law $p_r(\cdot)$; this thins clade-number moments into daughter-number moments. The Sackin mean follows from $S=\sum_r rC_r$ and $\sum_{r=2}^{n-1}\frac{2n}{r+1}+n=2n(H_n-1)$.

## Depends on

- [Clade-number and daughter-number bases of tree statistics](clade-number-and-daughter-number-bases.md)

## Sources

- Daniel J. Bauman, Noah A. Rosenberg, "Basis statistics for phylogenetic tree shape: tree balance formulas beyond expectations", arXiv:2610.40894 (2026), Theorems 5.3, 5.4, 5.10, 5.11, 6.1 and 6.2, <https://doi.org/10.48550/arXiv.2610.40894>
