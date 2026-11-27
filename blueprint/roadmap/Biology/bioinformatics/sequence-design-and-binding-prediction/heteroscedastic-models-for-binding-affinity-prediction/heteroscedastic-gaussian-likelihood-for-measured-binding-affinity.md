# Heteroscedastic Gaussian likelihood for measured binding affinity

Let $x$ be an input pair (a peptide and an MHC allele) and let the measured binding affinity $a(x)$ be the true affinity plus zero-mean noise whose scale may depend on $x$:

$$a(x) \mid x \ \sim\ \mathcal N\big(\mu_\theta(x),\ \sigma^2_\theta(x)\big),$$

with a model predicting both the mean $\mu_\theta$ and the variance $\sigma^2_\theta > 0$. Maximising the likelihood over a training set of pairs $(x_i, a_i)$ means minimising

$$\mathcal L_{\mathrm{aff}}(\theta) = \frac12 \sum_i \left( \frac{(a_i - \mu_\theta(x_i))^2}{\sigma^2_\theta(x_i)} + \log \sigma^2_\theta(x_i) \right) + \text{const},$$

so each example is weighted by its predicted precision and the $\log \sigma^2$ term penalises inflating the variance to escape a hard example. When some examples carry only an inequality constraint ($a_i \le c$ or $a_i \ge c$), their contribution is included only when the predicted mean violates the constraint. If the same model also predicts, from a binary presentation label $y_i$, a probability $p_\theta(x_i)$ of being a naturally presented ligand, the two parts are trained jointly against

$$\mathcal L(\theta) = \mathcal L_{\mathrm{aff}}(\theta) + \sum_i \mathrm{CE}\big(y_i, p_\theta(x_i)\big),$$

with each sum taken over the examples whose corresponding label is observed, so measured-affinity data and mass-spectrometry ligand data train one model.

## Remarks

With constant variance the first term reduces to ordinary least squares; letting the variance depend on the input makes the loss a heteroscedastic (negative log) Gaussian likelihood, in which the predicted $\sigma^2_\theta(x)$ reports how noisy the assay is believed to be for that input and automatically downweights unreliable measurements. The stationary point in $\sigma^2$ for fixed mean is $\sigma^2_\theta(x_i) = (a_i - \mu_\theta(x_i))^2$, which is why the two terms balance rather than drive the variance to zero or infinity. The censored treatment of inequality-labelled affinities is a one-sided hinge: within the stated bound the measurement carries no information about the mean. Zeng and Gifford (DeepLigand) combine this affinity head with a contextual peptide embedding and a ligand-presentation classifier, and report improved identification of MHC class I ligands over models trained on affinity alone.

## Sources

- H. Zeng, D. K. Gifford, "DeepLigand: accurate prediction of MHC class I ligands using peptide embedding", Bioinformatics 35 (2019), i278–i283, <https://doi.org/10.1093/bioinformatics/btz330> (PMC6612839), Section 2.2, "Model architecture and training".
