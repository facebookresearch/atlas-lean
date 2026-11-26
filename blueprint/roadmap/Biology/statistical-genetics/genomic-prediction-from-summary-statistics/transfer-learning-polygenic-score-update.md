# Transfer-learning update of a polygenic score

In a target population let $Y = \sum_{j=1}^{M} G_j \beta_j + C\gamma + \varepsilon$, where $G_j$ are genotype columns, $C$ the covariates (with intercept) and $\beta_j = \beta_j^{\mathrm{pre}} + \tau_j$, with $\beta_j^{\mathrm{pre}}$ the effects of a polygenic score pre-trained in a source population. TL-PRS minimizes the squared loss $\lVert Y - G\beta - C\gamma \rVert^2$ by gradient descent started at $\beta^{(0)} = \beta^{\mathrm{pre}}$:

$$\beta_j^{(r+1)} = \beta_j^{(r)} + \alpha\, G_j^\top \bigl(Y - G\beta^{(r)} - C\gamma\bigr),$$

with learning rate $\alpha$ and number of iterations chosen on a validation set (early stopping), updating within linkage-disequilibrium blocks. With summary statistics only, $G^\top Y$ is estimated from the target-population GWAS and $G^\top G$ from a reference panel of the target ancestry. Scores from several source ancestries are combined linearly, $\mathrm{PRS} = \pi\, \mathrm{PRS}_1 + (1 - \pi)\, \mathrm{PRS}_2$ with $\pi \in [0, 1]$, before or as the starting point of the update.

## Depends on

- [Effect-estimate model for polygenic score accuracy](prsmodel.md)

## Expansion

The loss has gradient $-2 G_j^\top (Y - G\beta - C\gamma)$ in $\beta_j$ and second derivative $2 G_j^\top G_j > 0$; the step size $\alpha = 2\alpha'$ absorbs the factor $2$. Because the update only needs $G^\top Y$ and $G^\top G$, it runs on summary statistics. Early stopping keeps the estimate near the source-population effects, which acts as shrinkage toward the prior model.

## Sources

- Z. Zhao et al., *The construction of cross-population polygenic risk scores using transfer learning*, Am. J. Hum. Genet. 109 (2022). <https://doi.org/10.1016/j.ajhg.2022.09.010> (PMCID: PMC9674947), Material and methods, Equation 1.
