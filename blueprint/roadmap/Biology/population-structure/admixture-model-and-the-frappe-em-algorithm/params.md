# Parameters of the admixture model

Let $I$ (individuals), $J$ (biallelic SNPs) and a finite set $K$ (ancestral populations) be given. Parameters $\theta = (Q, F)$ of the admixture model consist of real ancestry proportions $Q_{ik}$ ($i \in I$, $k \in K$) and reference-allele frequencies $F_{kj}$ ($k \in K$, $j \in J$) with

- $Q_{ik} > 0$ for all $i, k$, and $\sum_{k \in K} Q_{ik} = 1$ for every $i$;
- $0 < F_{kj} < 1$ for all $k, j$.

Strict positivity keeps every term of the log-likelihood finite.
