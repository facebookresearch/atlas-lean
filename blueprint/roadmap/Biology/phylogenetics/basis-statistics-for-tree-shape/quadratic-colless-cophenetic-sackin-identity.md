# Quadratic Colless, total cophenetic and Sackin identity

Let $T$ be a rooted binary tree with $n$ leaves. For an inner vertex $v$ with daughter clades of sizes $n_{v_1},n_{v_2}$ define the **quadratic Colless index** $QC(T)=\sum_{v\ \text{inner}}(n_{v_1}-n_{v_2})^2$, the **Sackin index** $S(T)=\sum_{x\ \text{leaf}}\delta_T(x)$ (sum of leaf depths), and the **total cophenetic index** $\Phi(T)=\sum_{\{x,y\}}\delta_T(\mathrm{lca}(x,y))$, summed over unordered pairs of distinct leaves. Then

$$QC(T)=2\Phi(T)+S(T)-n(n-1).$$

In particular $QC$ is represented by the clade-number basis: with $C_r(T)$ the number of clades of size $r$, $S(T)=\sum_{r=2}^n rC_r(T)$ and $\Phi(T)=\sum_{r=2}^{n-1}\binom r2C_r(T)$, so the Yule mean, variance and covariances of $QC$ follow from those of the clade numbers.

## Expansion

For an inner vertex $v$ with daughter sizes $a,b$ and $n_v=a+b$, $(a-b)^2=n_v^2-4ab$ and $ab=\binom{n_v}{2}-\binom a2-\binom b2$. Summing $ab$ over inner vertices telescopes, because every non-root inner clade appears once as a daughter and leaves contribute $\binom 12=0$: $\sum_v ab=\binom n2$. Also $\sum_v n_v^2=\sum_v\big(2\binom{n_v}{2}+n_v\big)=2\big(\Phi(T)+\binom n2\big)+S(T)$, using $\Phi(T)=\sum_{v\ne\rho}\binom{n_v}{2}$ and $S(T)=\sum_v n_v$. Hence $QC(T)=2\Phi(T)+S(T)+n(n-1)-2n(n-1)$.

## Depends on

- [Clade-number and daughter-number bases of tree statistics](clade-number-and-daughter-number-bases.md)

## Sources

- Daniel J. Bauman, Noah A. Rosenberg, "Basis statistics for phylogenetic tree shape: tree balance formulas beyond expectations", arXiv:2610.40894 (2026), Proposition 4.1 and Appendix D, <https://doi.org/10.48550/arXiv.2610.40894>
