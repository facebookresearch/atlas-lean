# Compatibility of local zero-inflated negative binomial conditionals requires competitive interactions

**Model.** Let $X_{is}$ be the count (for example the UMI count of gene $s \in V = \{1,\dots,p\}$ in cell $i$). A ZINB graphical model specifies, for every gene $s$ and conditioning set $K \subseteq V$, a zero-inflated negative binomial conditional law

$$f(x_{is} \mid \mathbf{x}_{i,K\setminus\{s\}}) = \pi_{is|K}\,\delta_0(x_{is}) + (1-\pi_{is|K})\,f_{\rm NB}(x_{is};\mu_{is|K},\theta_s),$$

with a log link for the NB mean and a logit link for the non-dropout probability:

$$\ln\mu_{is|K} = \nu^\mu_{s|K} + \sum_{t\in K\setminus\{s\}}\beta^\mu_{st|K}x_{it},\qquad \operatorname{logit}(1-\pi_{is|K}) = \nu^\pi_{s|K} + \sum_{t\in K\setminus\{s\}}\beta^\pi_{st|K}x_{it}.$$

Here $\theta_s$ is the inverse dispersion. An edge $s - t$ is absent exactly when $\beta^\mu_{st|K} = \beta^\mu_{ts|K} = \beta^\pi_{st|K} = \beta^\pi_{ts|K} = 0$ for all $K$. Taking $\pi \equiv 0$ gives NB models, and letting $\theta_s\to\infty$ gives Poisson graphical models.

**Theorem.** Let $\mathbf{X}_V = (X_1,\dots,X_p)$ have support $\mathcal{X}_V$, and suppose univariate conditional probability mass functions of the above ZINB form are given. A joint distribution with exactly these conditionals exists if and only if $\theta_s$ is constant for every $s\in V$ and all mean-regression coefficients $\beta^\mu_{st|K}$ are non-positive ($\beta^\mu_{st|K}\le 0$), for every $K\subseteq V$. The source's main text prints "negative" here; its supplementary proof of Theorem 3.1 treats $\beta^\mu_{st|K}\le 0$, and "negative" cannot be right: two independent ZINB counts have conditionals of this form with every $\beta^\mu_{st|K}=0$ (a missing edge) and their product as a joint law.

So a proper joint ZINB Markov random field can encode only competitive (non-positive) dependencies in the means. This is the count-data analogue of Besag's restriction for auto-Poisson models.

## Expansion

The proof follows Besag's analysis of auto-models. Compatible conditionals determine the joint law up to normalization through ratios of conditionals, and the resulting kernel must be summable over $\mathbb{N}^p$. Intuitively, a positive interaction in the log-mean lets counts reinforce each other without bound, so the normalizing sum diverges, as for the auto-Poisson model. Since gene networks contain positive associations, the paper does not use a joint likelihood. It learns the graph by neighbourhood selection with the PC-stable algorithm, testing $H_0: \beta^\mu_{st|K} = \beta^\pi_{st|K} = 0$ with the deviance $D_{s|K} = 2(\hat\ell_s - \hat\ell_s^0)$, which is asymptotically $\chi^2_2$, and treats the product of conditionals as a pseudo-likelihood.

## Sources

- T. K. H. Nguyen, K. Van den Berge, M. Chiogna and D. Risso, "Structure learning for zero-inflated counts, with an application to single-cell RNA sequencing data", arXiv:2011.12044 (2020), Section 3 (model specification, Theorem 3.1) and Section 4 (structure learning), <https://doi.org/10.48550/arXiv.2011.12044>.
