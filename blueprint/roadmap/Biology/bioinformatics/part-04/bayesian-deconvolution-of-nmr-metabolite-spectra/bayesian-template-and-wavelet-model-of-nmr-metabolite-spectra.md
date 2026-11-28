# Bayesian template-and-wavelet model of NMR metabolite spectra

A preprocessed frequency-domain $^1$H NMR spectrum of a biological mixture is a pair $(\mathbf x,\mathbf y)\in\mathbb{R}^n\times\mathbb{R}^n$ of chemical shifts and intensities. Model the $y_i$ as independent normals with

$$
\mathbb{E}(y_i\mid\mathbf x)=\phi(x_i)+\xi(x_i),\qquad \phi(\delta)=\sum_{m=1}^{M}\beta_m t_m(\delta),
$$

where $\beta_m\ge0$ is proportional to the concentration of cataloged metabolite $m$ and its signature template is a sum of multiplets of Lorentzian peaks with common width $\gamma$:

$$
t_m(\delta)=\sum_u z_{mu}\,g_{mu}(\delta-\delta^\star_{mu}),\qquad g_{mu}(\delta)=\sum_{v=1}^{V_{mu}}w_{muv}\,l_\gamma(\delta-c_{muv}),
$$

with $z_{mu}$ the proton count of multiplet $u$, $\delta^\star_{mu}$ its chemical shift (centre of mass), and peak weights $w_{muv}$ and offsets $c_{muv}$ fixed by the multiplet type and $J$-coupling constants. The residual signal $\xi$ of uncatalogued compounds is a linear combination of symlet-6 wavelets with coefficients $\boldsymbol\theta\in\mathbb{R}^p$. With $\mathcal W$ the wavelet transform and $\mathbf T=(t_m(x_i))$, the likelihood is the regression

$$
\mathcal W\mathbf y=\mathcal W\mathbf T\boldsymbol\beta+\boldsymbol\theta+\boldsymbol\epsilon,\qquad\boldsymbol\epsilon\sim N(0,\mathbf I_p/\lambda).
$$

Because $[\mathcal W\mathbf T\ \ \mathbf I_p]$ has more columns than rows, the two components are not identifiable in the likelihood; the prior separates them. Take $\beta_m\sim TN(e_m,1/s_m,0,\infty)$, a log-normal prior on $\gamma$, and for $(\boldsymbol\theta,\boldsymbol\psi,\boldsymbol\tau,\lambda)$ the joint density proportional to

$$
\lambda^{a+\frac{p+n}{2}-1}\prod_{jk}\psi_{jk}^{c_j-\frac12}e^{-\psi_{jk}d_j/2}\exp\!\Big(-\frac\lambda2\Big(b+\sum_{jk}\psi_{jk}\theta_{jk}^2+r\,\|\boldsymbol\tau-h\mathbf 1_n\|^2\Big)\Big)\,\mathbb 1\{\mathcal W^{-1}\boldsymbol\theta\ge\boldsymbol\tau,\ h\mathbf 1_n\ge\boldsymbol\tau\},
$$

with positive hyperparameters $a,b,c_j,d_j,r$ and a threshold $h$ slightly below zero.

**Lemma.** This density is normalisable: it defines a proper joint prior for $(\boldsymbol\theta,\boldsymbol\psi,\boldsymbol\tau,\lambda)$.

## Expansion

The gamma-distributed local precisions $\psi_{jk}$ give heavy-tailed, sparsity-inducing shrinkage on the wavelet coefficients, so unexplained structure is absorbed by $\xi$ only when the data demand it. The soft truncation $\mathcal W^{-1}\boldsymbol\theta\ge\boldsymbol\tau$ with smoothed limits $\boldsymbol\tau$ encodes that spectra lie mostly above the baseline, which stops the wavelet component from carving negative dips under metabolite multiplets and biasing $\boldsymbol\beta$. Placing the constraint on the joint rather than the conditional law of $\boldsymbol\theta$ avoids an intractable normalising constant, so block Gibbs and Metropolis updates are possible. In the limit $a,b,s_m\to0$ the prior is invariant under $(\boldsymbol\beta,\boldsymbol\theta,\lambda)\mapsto(S\boldsymbol\beta,S\boldsymbol\theta,\lambda/S^2)$, making inference independent of the measurement scale.

## Sources

- W. Astle, M. De Iorio, S. Richardson, D. Stephens, "A Bayesian Model of NMR Spectra for the Deconvolution and Quantification of Metabolites in Complex Biological Mixtures", Section 2 (Lemma 1). <https://doi.org/10.48550/arXiv.1105.2204>
