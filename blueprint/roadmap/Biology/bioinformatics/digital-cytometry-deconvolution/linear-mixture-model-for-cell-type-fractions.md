# Linear mixture model for cell type fractions

Let $n$ marker genes, $c$ cell types and $k$ bulk samples be given. Let

$$B \in \mathbb{R}^{n \times c}_{\ge 0}$$

be a *signature matrix* whose column $B_{\bullet,t}$ is the expression profile of cell type $t$ over the $n$ marker genes, and let $M' \in \mathbb{R}^{n \times k}_{\ge 0}$ hold the bulk profiles of the same $n$ genes, all in non-log linear space. The *fractional abundance matrix* $F \in \mathbb{R}^{c \times k}$ is required to satisfy

$$B\,F_{\bullet,j} = M'_{\bullet,j}, \qquad 1 \le j \le k, \qquad F_{t,j} \ge 0 \ \text{ for all } t,j,$$

with the system overdetermined, $n > c$. Under the additional normalization

$$\sum_{t=1}^{c} F_{t,j} = 1 \qquad (1 \le j \le k),$$

the column $F_{\bullet,j}$ is read as the vector of cell type proportions of sample $j$ with respect to the cell subsets represented in $B$.

In practice the equations hold only approximately and $F_{\bullet,j}$ is chosen to minimize a loss, for example by $\nu$-support vector regression, which fits a sparse robust linear model and is tolerant to noise, to cell types absent from $B$, and to collinearity among the columns of $B$.

## Expansion

The model says that a bulk transcriptome is an abundance-weighted sum of the transcriptomes of its constituent cell types, which holds when the measurement is linear in the number of transcripts contributed by each cell. Two scale ambiguities are intrinsic. First, replacing $B_{\bullet,t}$ by $\lambda_t B_{\bullet,t}$ and $F_{t,j}$ by $F_{t,j}/\lambda_t$ leaves the product unchanged, so fractions are identified only relative to the normalization of the reference profiles (cell types differ in total mRNA content, so the entries of $F$ are mRNA fractions rather than cell fractions until rescaled). Second, scaling a whole column of $M'$ scales the corresponding column of $F$, which the sum-to-one constraint removes.

Because $n > c$, the system is overdetermined and generically inconsistent in the presence of noise, so a solution is a minimizer rather than an exact root; nonnegativity keeps the estimate interpretable. Identifiability of the minimizer requires $B$ to have full column rank $c$, which fails when two reference profiles are collinear over the marker genes: this is why the marker set is selected for genes differentially expressed between subsets.

## Sources

- A. M. Newman, C. B. Steen, C. L. Liu, A. J. Gentles, A. A. Chaudhuri, F. Scherer, M. S. Khodadoust, M. S. Esfahani, B. A. Luca, D. Steiner, M. Diehn, A. A. Alizadeh, "Determining cell type abundance and expression from bulk tissues with digital cytometry", Nature Biotechnology 37 (2019) 773-782, Methods, "Overview of CIBERSORTx analytical framework", Equation (1), <https://doi.org/10.1038/s41587-019-0114-2> (PMC6610714).
