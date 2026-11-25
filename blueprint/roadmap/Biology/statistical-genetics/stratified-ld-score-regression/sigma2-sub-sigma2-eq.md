# LDSC-SEG contrast

Let $\mathcal{C}$ be a finite set of annotations, let $a_{kC} \in \mathbb{R}$ be annotation values of the markers and $\tau_C \in \mathbb{R}$ coefficients, let $c_S \in \mathcal{C}$, and let $k, k'$ be markers with $a_{kC} = a_{k'C}$ for every $C \ne c_S$. Then

$$\sum_{C} \tau_C\, a_{kC} - \sum_{C} \tau_C\, a_{k'C} = \tau_{c_S} (a_{k c_S} - a_{k' c_S}).$$

With per-SNP variances $\sigma^2_k = \sum_C \tau_C a_{kC}$, $c_S$ the indicator of a gene set $S$ contained in a control gene set $G$, $k \in S$ and $k' \in G \setminus S$ with equal values of all other annotations, this gives $\sigma^2_k - \sigma^2_{k'} = \tau_S$ (Finucane et al. 2018).

## Sources

- H. K. Finucane, Y. A. Reshef, V. Anttila, K. Slowikowski, A. Gusev, A. Byrnes, et al., *Heritability enrichment of specifically expressed genes identifies disease-relevant tissues and cell types*, Nat. Genet. 50 (2018), 621–629.
