# p-value mixture likelihood of a nested effects model

**Setting.** $n$ signaling genes (S-genes) are silenced one at a time by RNAi, and $m$ effect genes (E-genes) are measured. A network hypothesis is a directed graph $\Phi\in\{0,1\}^{n\times n}$ on the S-genes; each E-gene $i$ is attached to exactly one S-gene $\theta_i\in\{1,\dots,n\}$. Silencing S-gene $k$ is predicted to perturb E-gene $i$ exactly when $\theta_i$ is reachable from $k$ in $\Phi$ (including $\theta_i=k$). The data are an $m\times n$ matrix $D$ of differential-expression p-values $D_{ik}$ for E-gene $i$ after knockdown $k$.

**Marginal likelihood.** Assuming independent rows, independent knockdowns and independent attachments with prior $P(\theta_i=j\mid\Phi)$,

$$P(D\mid\Phi)=\prod_{i=1}^m\sum_{j=1}^n P(\theta_i=j\mid\Phi)\prod_{k=1}^n P(D_{ik}\mid\Phi,\theta_i=j),$$

where, modelling each p-value as a mixture of a uniform null and an alternative density $f_1$ on $[0,1]$,

$$P(D_{ik}\mid\Phi,\theta_i)=\begin{cases}f_1(D_{ik})&\text{if }\Phi\text{ predicts an effect of knockdown }k\text{ on E-gene }i,\\ 1&\text{otherwise,}\end{cases}\qquad f_1(p)=\pi_k+(1-\pi_k)\,\mathrm{Beta}(p;1,\beta_k).$$

The ratio $f_1(D_{ik})/1$ acts as a likelihood ratio: a predicted effect raises the score exactly when $f_1(D_{ik})>1$.

**Regularized posterior.** With independent Laplace priors $P(\Phi_{ij})\propto\exp(-\lambda|\Phi_{ij}-\hat\Phi_{ij}|)$ around prior edge beliefs $\hat\Phi$,

$$\log P(\Phi\mid D)=\log P(D\mid\Phi)-\lambda\sum_{i,j}|\Phi_{ij}-\hat\Phi_{ij}|+\text{const},$$

with $\lambda$ chosen to minimize the Akaike information criterion. Because predictions depend only on reachability, two hypotheses with the same transitive closure have the same likelihood (prediction equivalence), so the search can be restricted to transitively closed graphs.

## Expansion

Conditioning on the attachment $\theta_i$ and summing it out gives the mixture over $j$; independence of knockdowns factorizes the inner product. Under the null a p-value is uniform with density $1$, so an E-gene whose predicted effects coincide with small p-values contributes factors $f_1(D_{ik})\gg1$. Working with raw p-values replaces the discretization of the original nested effects model, which needed user-chosen type I and type II error rates.

## Sources

- H. Fröhlich, M. Fellmann, H. Sültmann, A. Poustka, T. Beißbarth, "Large scale statistical inference of signaling pathways from RNAi and microarray data", BMC Bioinformatics 8 (2007) 386. <https://doi.org/10.1186/1471-2105-8-386>, PMCID PMC2241646. Section "Generalized Inference Framework" and "Regularization".
