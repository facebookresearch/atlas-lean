# Nu-support vector regression deconvolution of cell-type fractions

**Mixture model.** Let $g$ marker genes and $c$ cell types be fixed, with $g > c$. A signature
matrix $B \in \mathbb{R}^{c \times g}$ holds in row $k$ the reference expression of cell type $k$ in
non-logarithmic (linear) space. A bulk mixture profile $m \in \mathbb{R}^{1 \times g}$ is modelled as

$$m = f \times B + \text{noise}, \qquad f \in \mathbb{R}^{1 \times c},\ f_k \ge 0,$$

so the problem is an overdetermined linear system in the unknown cell-type weights $f$. The stability
of the system to perturbations of $m$ is measured by the 2-norm condition number
$\kappa_2(B) = \sigma_{\max}(B) / \sigma_{\min}(B)$, and marker genes are chosen so that $\kappa_2(B)$
is small.

**Estimator.** Standardize $m$ and every column of the regression (each of the $c$ predictors) to
mean $0$ and variance $1$ across the $g$ genes. Treat the genes $j = 1, \dots, g$ as observations with
response $m_j$ and predictor vector $b_j = (B_{1j}, \dots, B_{cj})$, and fit a linear-kernel
$\nu$-support vector regression, with $\nu \in (0, 1]$ and $C > 0$:

$$\min_{w,\, w_0,\, \varepsilon \ge 0,\, \xi,\, \xi^*}\ \ \frac{1}{2}\lVert w \rVert_2^2 + C\Bigl(\nu \varepsilon + \frac{1}{g}\sum_{j=1}^{g} (\xi_j + \xi_j^*)\Bigr)$$

subject to $m_j - (w \cdot b_j + w_0) \le \varepsilon + \xi_j$,
$(w \cdot b_j + w_0) - m_j \le \varepsilon + \xi_j^*$ and $\xi_j, \xi_j^* \ge 0$. The loss is the
linear $\varepsilon$-insensitive loss: genes fitted within the tube of half-width $\varepsilon$ cost
nothing, and the remaining genes (the support vectors) alone determine $w$. The deconvolution is then

$$\hat f_k = \frac{\max(w_k, 0)}{\sum_{l=1}^{c} \max(w_l, 0)}, \qquad k = 1, \dots, c,$$

that is, negative coefficients are set to $0$ and the rest are renormalized to sum to $1$, giving
relative (not absolute) fractions. This requires $w_l > 0$ for some $l$; when every coefficient is
nonpositive the fit returns no fractions for that value of $\nu$. The fit is repeated for $\nu \in \{0.25, 0.5, 0.75\}$, and the
$\hat f$ with the smallest root mean squared error between $m$ and $\hat f \times B$ among the fits that
return fractions is kept; if none does, the sample has no estimate.

## Remarks

The parameter $\nu$ is an upper bound on the fraction of genes lying outside the tube and a lower
bound on the fraction of support vectors (the $\nu$-property of Schölkopf et al.), so larger $\nu$
gives a narrower tube and more genes used. Two features make the estimator robust for deconvolution.
The linear loss grows more slowly than the squared loss of least squares, so genes that the linear
mixture fits badly (noise, or cell types absent from $B$) have bounded influence, and the
support-vector selection acts as a second, adaptive round of gene selection within the signature.
The ridge-type $L_2$ penalty $\frac{1}{2}\lVert w \rVert_2^2$ shrinks the weights of highly correlated
predictors toward each other, which counters the multicollinearity of closely related cell types.

## Sources

- A. M. Newman, C. L. Liu, M. R. Green, A. J. Gentles, W. Feng, Y. Xu, C. D. Hoang, M. Diehn,
  A. A. Alizadeh, "Robust enumeration of cell subsets from tissue expression profiles", Nature
  Methods 12 (2015) 453-457, Online Methods, "Deconvolution model", "Signature matrix" and
  "Support vector regression (SVR)", <https://doi.org/10.1038/nmeth.3337> (PMC4739640).
- B. Schölkopf, A. J. Smola, R. C. Williamson, P. L. Bartlett, "New support vector algorithms",
  Neural Computation 12 (2000) 1207-1245, <https://doi.org/10.1162/089976600300015565>.
