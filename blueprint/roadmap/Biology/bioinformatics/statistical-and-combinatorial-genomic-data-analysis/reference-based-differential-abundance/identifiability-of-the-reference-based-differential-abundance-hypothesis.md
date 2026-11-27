# Identifiability of the reference-based differential abundance hypothesis

Let $A=(A_1,\dots,A_d)\ge0$ be the absolute abundances of $d$ components (for example taxa), observed only through multinomial counts $N\mid P,N^*\sim\mathrm{Multinomial}(N^*,P)$ with relative abundance $P_i=A_i/\sum_jA_j$. For two populations $\pi_1,\pi_2$ let $Q_{k,i}=\mathbb E_{\pi_k}(P_i)$ be the expected relative abundance of component $i$. A set $I_0\subseteq[d]$ is a *reference set* if there is a constant $b>0$ with

$$
Q_{1,i}=b\,Q_{2,i}\qquad(i\in I_0),
$$

so that ratios inside $I_0$ do not change between the populations. The reference-based hypotheses are

$$
H_{i,0}:\ \frac{Q_{1,i}}{\sum_{j\in I_0}Q_{1,j}}=\frac{Q_{2,i}}{\sum_{j\in I_0}Q_{2,j}}\qquad\text{vs.}\qquad H_{i,1}:\ \text{the two ratios differ}.
$$

**Proposition.** If the reference set satisfies $|I_0|>d/2$, these hypotheses are well defined: any two reference sets with more than $d/2$ elements give the same nulls. Without that condition they can fail. There are instances with two reference sets $I_{0,1},I_{0,2}$, each of size at most $d/2$, whose null hypotheses contradict each other.

## Proof sketch

Two reference sets of size more than $d/2$ intersect. A component in the intersection forces both sets to have the same scale factor $b$, so they define the same null for every component. For sets of size at most $d/2$, take two disjoint halves that are each internally proportional with different scale factors; each half is a valid reference set and declares the other half differential. The hypothesis on absolute abundances, $\mathbb E_{\pi_1}A_i=\mathbb E_{\pi_2}A_i$, cannot be tested consistently from compositions alone. The reference-based hypothesis agrees with it when absolute abundances inside $I_0$ are unchanged.

## Sources

- Shulei Wang, "Robust differential abundance test in compositional data", *Biometrika* 110 (2023), 169–185, <https://doi.org/10.1093/biomet/asac029>. Preprint version: arXiv:2101.08765 (2021), Section 2 (model Eq. (1), reference set and reference-based hypothesis) and Proposition 1, <https://doi.org/10.48550/arXiv.2101.08765>.
