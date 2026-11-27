# Information partial directed coherence and mutual information rate

**Setting.** Let $\mathbf x(n)=[x_1(n),\dots,x_K(n)]^{\top}$ be a zero-mean wide-sense stationary multichannel signal, for example local field potentials or EEG from $K$ brain areas, with autoregressive and moving-average representations

$$\mathbf x(n)=\sum_{l\ge1}\mathbf A(l)\mathbf x(n-l)+\mathbf w(n)=\sum_{l\ge0}\mathbf H(l)\mathbf w(n-l),$$

where the innovations $\mathbf w$ have positive definite covariance $\boldsymbol\Sigma_{\mathbf w}=(\sigma_{ij})$. Let $\bar A_{ij}(\omega)=\delta_{ij}-\sum_{l\ge1}a_{ij}(l)e^{-\mathrm j\omega l}$, $\bar{\mathbf a}_j=(\bar A_{1j},\dots,\bar A_{Kj})^{\top}$, $\bar H_{ij}(\omega)=\sum_{l\ge0}h_{ij}(l)e^{-\mathrm j\omega l}$, and $\bar{\mathbf h}_j=(\bar H_{j1},\dots,\bar H_{jK})^{\top}$. Define the *information PDC* and *information DTF* from $j$ to $i$:

$$\iota\pi_{ij}(\omega)=\frac{\bar A_{ij}(\omega)\,\sigma_{ii}^{-1/2}}{\sqrt{\bar{\mathbf a}_j^H(\omega)\boldsymbol\Sigma_{\mathbf w}^{-1}\bar{\mathbf a}_j(\omega)}},\qquad \iota\gamma_{ij}(\omega)=\frac{\bar H_{ij}(\omega)\,\rho_{jj}^{1/2}}{\sqrt{\bar{\mathbf h}_j^H(\omega)\boldsymbol\Sigma_{\mathbf w}\bar{\mathbf h}_j(\omega)}},$$

where $\rho_{jj}$ is the variance of the partialized innovation $\zeta_j(n)=w_j(n)-\mathbf E[w_j(n)\mid w_l(n),\ l\neq j]$. These reduce to the classical partial directed coherence and directed transfer function when $\boldsymbol\Sigma_{\mathbf w}=I$.

**Theorem.** Let $\eta_j(n)=x_j(n)-\mathbf E[x_j(n)\mid x_l(m),\ l\neq j,\ m\in\mathbb Z]$ be the partialized process of $x_j$ given all other channels at all times, and let $C_{uv}(\omega)$ denote the coherence. Then

$$\iota\pi_{ij}(\omega)=C_{w_i\eta_j}(\omega),\qquad \iota\gamma_{ij}(\omega)=C_{x_i\zeta_j}(\omega).$$

If $\mathbf x$ is Gaussian, the mutual information rates are

$$\mathrm{MIR}(w_i,\eta_j)=-\frac1{4\pi}\int_{-\pi}^{\pi}\log\big(1-|\iota\pi_{ij}(\omega)|^2\big)\,d\omega,\qquad \mathrm{MIR}(x_i,\zeta_j)=-\frac1{4\pi}\int_{-\pi}^{\pi}\log\big(1-|\iota\gamma_{ij}(\omega)|^2\big)\,d\omega .$$

## Proof sketch

The Gelfand–Yaglom formula expresses the mutual information rate of two jointly Gaussian stationary series as $-\frac1{4\pi}\int\log(1-|C_{xy}|^2)$. The theorem identifies $\iota$PDC and $\iota$DTF as genuine coherences between specific processes, so their squared moduli are frequency-resolved shares of mutual information. A key step is the spectral identity $\bar{\mathbf a}_j^H\boldsymbol\Sigma_{\mathbf w}^{-1}\bar{\mathbf a}_j=S_{\eta_j\eta_j}^{-1}$, the inverse spectrum of the partialized process. So $\iota$PDC measures how much the innovation driving area $i$ shares with what is unique to area $j$ (direct, Granger-type influence). $\iota$DTF measures how much the activity of area $i$ shares with the new information injected at $j$ (total, direct plus indirect, influence). Normalizing by the full innovation covariance $\boldsymbol\Sigma_{\mathbf w}$, rather than the identity or its diagonal, is what makes this information-theoretic identification exact.

## Sources

- Daniel Y. Takahashi, Luiz A. Baccalá and Koichi Sameshima, "Information theoretic interpretation of frequency domain connectivity measures", *Biological Cybernetics* 103 (2010), 463–469, <https://doi.org/10.1007/s00422-010-0410-x>. Preprint version: arXiv:1012.0353 (2010), Section 2 (autoregressive model, definitions of $\iota$PDC and $\iota$DTF), Theorem 1 and Corollary 1 (PDC), Theorem 2 and Corollary 2 (DTF), Lemma 1 (inverse partial spectrum), Theorem 3 (Gelfand–Yaglom), <https://doi.org/10.48550/arXiv.1012.0353>.
