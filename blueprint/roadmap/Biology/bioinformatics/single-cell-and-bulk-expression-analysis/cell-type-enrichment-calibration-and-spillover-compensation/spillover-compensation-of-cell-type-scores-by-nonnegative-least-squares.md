# Spillover compensation of cell-type scores by nonnegative least squares

Let $T \in \mathbb{R}^{C \times N}$ be [calibrated cell-type scores](power-law-calibration-of-cell-type-enrichment-scores.md) (rows are cell types, columns samples), and let the cell types carry a two-level hierarchy in which each type is either a top-level type or a child of exactly one top-level type. From synthetic mixtures containing $25\%$ of one cell type, let $S_{xy} > 0$ be the calibrated score of cell type $x$ in the mixture of cell type $y$ (rows are scores, columns are mixtures). The spillover matrix normalizes each row by its own diagonal entry,

$$K_{xy} = \frac{S_{xy}}{S_{xx}}, \qquad K_{xx} = 1,$$

so $K_{xy}$ is the score of type $x$ in the mixture of type $y$ relative to the score of type $x$ in its own mixture. This is a row-relative ratio; it differs from the ratio $S_{xy}/S_{yy}$ to the score of type $y$ in its own mixture whenever $S_{xx} \ne S_{yy}$. The matrix is then cleaned so that no parent is compensated against a descendant: an off-diagonal entry $K_{xy}$ is kept only when $x$ and $y$ are both top-level types, or when $x$ is a child type and $y$ is either another child of the same parent or a top-level type other than that parent; every other off-diagonal entry is set to $0$. The kept off-diagonal entries are capped at $0.5$ and multiplied by a scaling parameter $\alpha \in [0,1]$ ($\alpha = 0.5$ in the source). Write $K_\alpha$ for the resulting matrix. For each sample $j$, the compensated score vector is

$$\hat{x}^{(j)} \in \arg\min_{x \in \mathbb{R}^{C},\ x \ge 0}\ \bigl\lVert K_{\alpha}\, x - T_{\cdot j} \bigr\rVert_2^2 .$$

Under the linear model $T_{\cdot j} = K_\alpha\, a^{(j)}$ with true abundance vector $a^{(j)} \ge 0$ and $K_\alpha$ invertible, $a^{(j)}$ is the unique minimizer (the objective is $0$ there and strictly convex because $K_\alpha$ has full rank), so compensation exactly removes the leakage modelled by $K_\alpha$.

## Depends on

- [Power-law calibration of cell-type enrichment scores](power-law-calibration-of-cell-type-enrichment-scores.md)

## Remarks

The construction copies fluorescence compensation in flow cytometry, where a detector reading is a linear combination of the dyes present and a spillover matrix measured on single-stain controls is inverted. Here a gene signature for one cell type also partially responds to closely related cell types (for example CD4+ and CD8+ T cells), so a pure sample of one inflates the scores of the other. The nonnegativity constraint keeps abundances physical; the cap, the parent-descendant zeroing and the factor $\alpha$ shrink the compensation because full inversion was observed to erase real correlations between signatures and their own cell types.

## Sources

- D. Aran, Z. Hu, A. J. Butte, "xCell: digitally portraying the tissue cellular heterogeneity landscape", Genome Biology 18 (2017) 220, Methods, "Learning the spillover compensation reference matrix" (row normalization by the diagonal; allowed parent and child pairings; cap at $0.5$) and "Calculating scores for a mixture", step (4). <https://doi.org/10.1186/s13059-017-1349-1> (PMC5688663)
