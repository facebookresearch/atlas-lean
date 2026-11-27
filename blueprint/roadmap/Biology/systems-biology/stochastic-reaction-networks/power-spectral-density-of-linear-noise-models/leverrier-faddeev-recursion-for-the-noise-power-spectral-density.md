# Leverrier–Faddeev recursion for the noise power spectral density

**Setting.** Near a stable fixed point, many stochastic biological systems (gene expression, neuron models such as FitzHugh–Nagumo or Hindmarsh–Rose, predator–prey models) reduce to a linear time-invariant (LTI) stochastic system

$$\dot{\mathbf x}(t) = -\mathbf J\,\mathbf x(t) + \mathbf L\,\boldsymbol\eta(t), \qquad \mathbf x(t) \in \mathbb R^n,$$

where $\boldsymbol\eta$ is Gaussian white noise with diffusion matrix $\mathbf D$, $\mathbf C = \mathbf L \mathbf D \mathbf L^\top$ is the input covariance, and $\mathbf J$ is the (sign-reversed) Jacobian, assumed to have all eigenvalues with positive real part so that a stationary state exists. Fourier transforming gives the stationary power spectral density (PSD) matrix

$$\boldsymbol{\mathcal S}(\omega) = (i\omega \mathbf I + \mathbf J)^{-1}\, \mathbf C\, (-i\omega \mathbf I + \mathbf J)^{-\top}, \qquad \omega \in \mathbb R .$$

**Theorem.** $\boldsymbol{\mathcal S}(\omega)$ is the rational function

$$\boldsymbol{\mathcal S}(\omega) = \frac{\sum_{\alpha=0}^{n-1} \mathbf P_\alpha\, \omega^{2\alpha} + i\omega \sum_{\alpha=0}^{n-2} \mathbf P'_\alpha\, \omega^{2\alpha}}{\sum_{\alpha=0}^{n} q_\alpha\, \omega^{2\alpha}},$$

whose coefficients are computed without any matrix inversion:

1. Numerator: starting from $\mathbf P_n = \mathbf P'_n = \mathbf 0$, for $\alpha = n, n-1, \dots, 1$,

$$\mathbf P'_{\alpha-1} = \mathbf J \mathbf P_\alpha - \mathbf P_\alpha \mathbf J^\top - \mathbf J \mathbf P'_\alpha \mathbf J^\top, \qquad \mathbf P_{\alpha-1} = q_\alpha \mathbf C + \mathbf P'_{\alpha-1}\mathbf J^\top - \mathbf J \mathbf P'_{\alpha-1} - \mathbf J \mathbf P_\alpha \mathbf J^\top .$$

2. Denominator: $q_n = 1$ and, for $\alpha < n$,

$$q_\alpha = \frac{1}{n-\alpha}\Big[\operatorname{Tr}\big(\mathbf J \mathbf Q'_{\alpha-1}\big) + \operatorname{Tr}\big(\mathbf J \mathbf Q_\alpha \mathbf J^\top\big)\Big],$$

where $\mathbf Q_\alpha, \mathbf Q'_\alpha$ obey the same recursion as $\mathbf P_\alpha, \mathbf P'_\alpha$ with $\mathbf C$ replaced by $\mathbf I$, started from $\mathbf Q_n = \mathbf Q'_n = \mathbf 0$ and with $\mathbf Q_{-1} = \mathbf Q'_{-1} = \mathbf 0$.

The matrices $\mathbf P_\alpha$ are symmetric and $\mathbf P'_\alpha$ antisymmetric, so the diagonal entries (auto-spectra) are real even functions of $\omega$, and the denominator is $Q(\omega) = \prod_{j=1}^n (\lambda_j^2 + \omega^2)$ with $\lambda_j$ the eigenvalues of $\mathbf J$.

## Proof sketch

Write $\boldsymbol{\mathcal S}(\omega) = \mathbf N(\omega)/Q(\omega)$ and multiply out $(i\omega\mathbf I + \mathbf J)\,\boldsymbol{\mathcal S}\,(-i\omega \mathbf I + \mathbf J)^\top = \mathbf C$; matching powers of $\omega$ yields the numerator recursion. The denominator coefficients come from a trace identity in the spirit of the Leverrier–Faddeev (Barnett–Leverrier) algorithm for the characteristic polynomial: $\operatorname{Tr}\,\mathcal L\{e^{i t \mathbf J} + e^{-i t \mathbf J}\}(\omega) = Q'(\omega)/Q(\omega)$, i.e. $\sum_j 2\omega/(\omega^2 + \lambda_j^2) = Q'/Q$, which turns the logarithmic derivative of $Q$ into Newton-type identities for the $q_\alpha$. The same method gives an inverse-free recursion for the discrete-time sum $\sum_{j,k \ge 0} \mathbf G^j \mathbf Y (\mathbf G^\top)^k$ with $\mathbf G$ convergent.

## Sources

- Shivang Rawat and Stefano Martiniani, "Element-wise and recursive solutions for the power spectral density of biological stochastic dynamical systems at fixed points", *Physical Review Research* 6 (2024), 043179, <https://doi.org/10.1103/physrevresearch.6.043179>. Preprint version: arXiv:2305.19890 (2023), recursive solution theorem (Leverrier–Faddeev-type algorithm), trace lemma and the discrete-time series theorem, <https://doi.org/10.48550/arXiv.2305.19890>.
