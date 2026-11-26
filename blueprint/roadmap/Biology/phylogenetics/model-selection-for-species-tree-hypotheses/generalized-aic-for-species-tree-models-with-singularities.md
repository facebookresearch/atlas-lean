# Generalized AIC for species-tree models with singularities

**Setting.** Data $\mathcal Z_n$ are $n$ i.i.d. observations from a regular full model with parameter space $\Theta$ (for example multinomial counts), and a candidate submodel has a closed parameter space $\Theta_0\subseteq\Theta$ that may contain boundary points or singularities. After centring and rescaling by the Fisher information at the true parameter $\theta_0$, the sample mean $\bar z_n$ is asymptotically $\mathcal N(\mu_0,I)$ on the image $\mathcal M$ of $\Theta$, the submodel becomes a set $\mathcal M_0$ whose local geometry near $\mu_0$ is a cone, and the maximum-likelihood estimate corresponds asymptotically to the Euclidean projection $\hat\mu_n$ of $\bar z_n$ onto $\mathcal M_0$. The **generalized AIC** is
$$\mathrm{AICg}=-2\log L(\hat\theta_n\mid\mathcal Z_n)+2\,\mathbb E_0\bigl[(\bar z_n-\mu_0)^{\mathsf T}(\hat\mu_n-\mu_0)\bigr].$$
For three species under the multispecies coalescent, the rooted gene-tree triplet frequencies $\mathbf p=(p_1,p_2,p_3)$ lie in the open simplex $\Delta^2$; model $T1$ (a fixed species-tree topology) has $\Theta_0=\{p_1\ge p_2=p_3\}$, a segment with a boundary at the star-tree centroid, and model $T3$ (any of the three topologies) is the union of three such segments, with a singularity at the centroid.

**Theorem 3.1.** Under the paper's regularity assumptions (holding for all models above), $\mathbb E_0[\mathrm{AICg}]-\Delta_n(\Theta_0,\theta_0)\to0$ at every $\theta_0\in\Theta_0$, including boundary points and singularities, where $\Delta_n$ is the expected Kullback-Leibler discrepancy targeted by AIC. The usual AIC, with penalty $2\dim\Theta_0$, does not have this property at singular points.

**Proposition 3.2.** The bias correction is asymptotically nonnegative: $\mathbb E_0[(\bar z_n-\mu_0)^{\mathsf T}(\hat\mu_n-\mu_0)]\ge0$.

**Proposition 4.1 (model $T1$).** $\mathrm{AICg}=-2\log L(\hat\theta_n\mid\mathcal Z_n)+1+\operatorname{erf}(\mu_{0,y}/\sqrt2)$, where $\mu_{0,y}\ge0$ is the transformed distance of the true parameter from the star-tree point along the segment. The penalty rises from $1$ at the star tree to the classical value $2$ far from it.

**Corollaries 4.4 and 4.5 (multiple half-lines).** If $\mathcal M_0$ is locally $l$ rays from $\mu_0$ at equal angles $2\pi/l$, then $\mathrm{AICg}=-2\log L+1$ for $l=1$ and $-2\log L+2+\frac{l}{\pi}\sin\frac{2\pi}{l}$ for $l\ge2$; as $l\to\infty$ the penalty tends to $4$. For $l=3$ this is the penalty of model $T3$ at the star tree.

## Expansion

The AIC bias correction is twice the expected covariance between the data and the fitted value. In a regular model the projection onto a $k$-dimensional affine space gives covariance $k$, recovering $2k$. At a boundary or singularity the projection is onto a cone, so the covariance depends on its shape: for a half-line starting at $\mu_0$ the projection keeps the normal coordinate only when it points into the line, which gives $1/2$ instead of $1$, and moving $\mu_0$ along the line interpolates through the error function; and for a union of rays the fitted value can jump between rays, adding covariance beyond the dimension count. Away from the singular point the correction converges to the regular value, but slowly, which is why the generalized form matters for species trees with short internal branches.

## Sources

- J. D. Mitchell, E. S. Allman, J. A. Rhodes, "A generalized AIC for models with singularities and boundaries", arXiv preprint (2022), Theorem 3.1, Proposition 3.2, Proposition 4.1, Proposition 4.3, Corollaries 4.4 and 4.5, <https://doi.org/10.48550/arXiv.2211.04136>.
