# Group-mode expression purification by nonnegative least squares

Let $M \in \mathbb{R}^{n \times k}_{\ge 0}$ hold $k$ bulk expression profiles over $n$ genes and let $F \in \mathbb{R}^{c \times k}_{\ge 0}$ be a [cell type fraction matrix](linear-mixture-model-for-cell-type-fractions.md) with $\sum_{t} F_{t,j} = 1$ for every sample $j$, obtained either by deconvolution or by direct measurement of composition. A *representative* cell-type expression matrix $H \in \mathbb{R}^{n \times c}$ is required to satisfy, for every gene $i$,

$$H_{i,\bullet}\,F = M_{i,\bullet}, \qquad H_{i,t} \ge 0 \ \text{ for all } t,$$

that is, $\sum_{t=1}^{c} H_{i,t} F_{t,j} = M_{i,j}$ for $1 \le j \le k$. The system is overdetermined exactly when $k > c$, and the estimate is the nonnegative least squares solution

$$\hat{H}_{i,\bullet} = \arg\min_{h \in \mathbb{R}^{c}_{\ge 0}} \bigl\lVert F^{\top} h^{\top} - M_{i,\bullet}^{\top} \bigr\rVert_2^2 .$$

Each gene is solved independently, so the problem decomposes into $n$ nonnegative least squares problems in $c$ unknowns with the same design matrix $F^{\top}$.

## Depends on

- [Linear mixture model for cell type fractions](linear-mixture-model-for-cell-type-fractions.md)

## Remarks

This is the transpose of the fraction problem: there the mixing matrix was known and the weights unknown; here the weights are known and the profiles unknown. Writing the mixture identity $M_{i,j} = \sum_t H_{i,t} F_{t,j}$ for the single gene $i$ gives $k$ linear equations in the $c$ unknowns $H_{i,1}, \dots, H_{i,c}$, so a unique least squares minimizer exists as soon as $F^{\top}$ has full column rank $c$, which needs $k \ge c$ samples whose compositions span the simplex directions; the more the compositions vary across the $k$ samples, the better conditioned $F^{\top}$ is and the more accurate the recovered profiles.

The output is a single profile per cell type for the whole sample set, so contrasts between conditions require re-solving on each group of samples separately; that limitation is what the sample-resolved decomposition addresses.

The nonnegativity constraint matters: an unconstrained least squares fit can return negative expression for a cell type that is rare in every sample, and the constrained minimizer sets such coordinates to zero instead.

## Sources

- A. M. Newman, C. B. Steen, C. L. Liu, A. J. Gentles, A. A. Chaudhuri, F. Scherer, M. S. Khodadoust, M. S. Esfahani, B. A. Luca, D. Steiner, M. Diehn, A. A. Alizadeh, "Determining cell type abundance and expression from bulk tissues with digital cytometry", Nature Biotechnology 37 (2019) 773-782, Methods, "Group-mode expression purification", Equation (2), <https://doi.org/10.1038/s41587-019-0114-2> (PMC6610714).
