# Nuclear-norm form of the ZINB-WaVE factor penalty

**Lemma.** For any real matrix $R$ and positive scalars $s, t$,

$$\min_{S,T:\ R = ST}\ \frac12\big(s\|S\|^2 + t\|T\|^2\big) = \sqrt{st}\,\|R\|_*,$$

where $\|\cdot\|$ is the Frobenius norm and $\|R\|_* = \operatorname{tr}\big((R^\top R)^{1/2}\big)$ is the nuclear norm. If $R = R_L R_\Sigma R_R$ is a singular value decomposition, a minimizer is

$$S = (t/s)^{1/4} R_L R_\Sigma^{1/2}, \qquad T = (s/t)^{1/4} R_\Sigma^{1/2} R_R .$$

**Corollary (balanced penalty).** For an $n \times J$ matrix $R$ and $\epsilon > 0$,

$$\min_{W,\alpha:\ R = W\alpha}\ \frac{\epsilon}{2}\Big(\frac1n\|W\|^2 + \frac1J\|\alpha\|^2\Big) = \frac{\epsilon}{\sqrt{nJ}}\|R\|_*,$$

attained at $W = (n/J)^{1/4}R_L R_\Sigma^{1/2}$, $\alpha = (J/n)^{1/4}R_\Sigma^{1/2}R_R$. At this optimum, for each factor $k \le \min(n,J)$,

$$\frac1n\sum_{i=1}^n W_{ik}^2 = \frac1J\sum_{j=1}^J \alpha_{kj}^2 = \frac{(R_\Sigma)_{kk}}{\sqrt{nJ}},$$

so the entries of $W$ and $\alpha$ have comparable scale.

Consequently, at any local maximum of the ZINB-WaVE penalized log-likelihood (with penalty weights $\epsilon_W, \epsilon_\alpha$ on $\|W\|^2$ and $\|\alpha\|^2$), $\epsilon_W W^\top W = \epsilon_\alpha\,\alpha\alpha^\top$, and an orthogonal change $(W, \alpha) \mapsto (WQ, Q^\top\alpha)$ gives an equivalent local maximum in which $W$ and $\alpha^\top$ have orthogonal columns; this is the representative the orthogonalization step chooses. (The source states that every local maximum has orthogonal columns, which fails because the penalized likelihood is invariant under these orthogonal changes.)

## Depends on

- [ZINB-WaVE regression model and penalized likelihood](zinb-wave-regression-model-and-penalized-likelihood.md)

## Expansion

Rescale $\tilde S = \sqrt{s}\,S$, $\tilde T = \sqrt{t}\,T$, $\tilde R = \sqrt{st}\,R$; the problem becomes $\min_{\tilde S\tilde T = \tilde R}\frac12(\|\tilde S\|^2 + \|\tilde T\|^2)$, whose value is the classical variational characterization $\|\tilde R\|_*$, attained at $\tilde S = \tilde R_L\tilde R_\Sigma^{1/2}$, $\tilde T = \tilde R_\Sigma^{1/2}\tilde R_R$. Since $\tilde R$ has the same singular vectors as $R$ and singular values multiplied by $\sqrt{st}$, undoing the scaling gives the stated minimizer. The corollary is the case $s = \epsilon/n$, $t = \epsilon/J$, the default ZINB-WaVE weights. Because the likelihood depends on $(W,\alpha)$ only through $W\alpha$, every optimal split of a given product is a rotation $(SQ, Q^\top T)$ of the balanced SVD split, and the SVD split itself has orthogonal columns.

## Sources

- D. Risso, F. Perraudeau, S. Gribkova, S. Dudoit, J.-P. Vert, "A general and flexible method for signal extraction from single-cell RNA-seq data", Nature Communications 9 (2018) 284, Methods, Lemma 1 and Corollary 1, <https://doi.org/10.1038/s41467-017-02554-5>, PMCID PMC5773593.
