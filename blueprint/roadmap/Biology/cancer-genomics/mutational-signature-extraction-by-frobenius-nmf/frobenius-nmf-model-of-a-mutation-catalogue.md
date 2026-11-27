# Frobenius-norm non-negative factorization of a mutation catalogue

Let $A \in \mathbb{R}_{\ge 0}^{N \times M}$ be a mutation catalogue whose entry $A_{nm}$ is the number of somatic substitutions of mutation class $n$ in sample $m$; with the six base-substitution classes refined by the immediately flanking $5'$ and $3'$ bases, $N = 6 \cdot 4 \cdot 4 = 96$. For a fixed rank $k$, signature extraction solves

$$\min_{W \in \mathbb{R}_{\ge 0}^{N \times k},\ H \in \mathbb{R}_{\ge 0}^{k \times M}} \tfrac{1}{2} \big\lVert A - WH \big\rVert_F^2 , \qquad A = WH + U,$$

where column $j$ of $W$ is the $j$-th mutational signature, a non-negative profile over the $N$ mutation classes, row $j$ of $H$ gives the exposure of each sample to that signature, and $U$ is the residual. The reconstruction $\widehat{A} = WH$ satisfies $\widehat{A}_{nm} = \sum_{j=1}^{k} W_{nj} H_{jm}$, so each sample's catalogue is modelled as a non-negative mixture of the same $k$ signatures.

## Remarks

The model says that each mutational process acts with a fixed probability profile over sequence contexts and that catalogues differ only in how long and how strongly each process operated, which is precisely a non-negative mixture. Non-negativity is what makes the factors interpretable as processes: unconstrained factorizations of the same rank fit at least as well but mix positive and negative contributions that no mechanism can produce. The Frobenius objective is the Gaussian-error choice and is minimized by multiplicative update rules that preserve non-negativity and do not increase the objective; it is not jointly convex, so solutions depend on initialization, and repeated runs are needed. The factorization is also only identified up to a scaling $W \to WD$, $H \to D^{-1}H$ with $D$ positive diagonal, and up to permutation of the $k$ components; a reported signature is a column of $W$ after a fixed normalization. A systematic sequencing artifact that recurs with a reproducible context profile is indistinguishable from a biological process in this model.

## Sources

- Nik-Zainal S, Alexandrov LB, Wedge DC, et al. Mutational processes molding the genomes of 21 breast cancers. *Cell* 149:979-993 (2012), Extended Experimental Procedures, "Nonnegative matrix factorization". DOI <https://doi.org/10.1016/j.cell.2012.04.024>. PMCID PMC3414841.
- Lee DD, Seung HS. Learning the parts of objects by non-negative matrix factorization. *Nature* 401:788-791 (1999). DOI <https://doi.org/10.1038/44565>.
