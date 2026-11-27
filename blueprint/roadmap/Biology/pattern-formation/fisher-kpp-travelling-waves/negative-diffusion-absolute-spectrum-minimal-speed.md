# Absolute spectrum and the minimal speed of negative-diffusion logistic fronts

This page covers the spectral result of Li, van Heijster, Marangell and Simpson (2020), Section 3, for the travelling waves on [smooth monotone travelling waves of a logistic equation with sign-changing aggregation diffusivity](negative-diffusion-logistic-travelling-waves.md). Notation is as there: $U_t = (D(U)U_x)_x + \lambda U(1-U)$ with $D(0) = D_i$, $D(1) = D_g$, $D_i > 4D_g > 0$, $c^* = 2\sqrt{\lambda D_i}$ and $c_\beta = 2\sqrt{D'(\beta)R(\beta)} < c^*$.

**Linearisation.** For a travelling wave $\hat u(z)$, $z = x - ct$, of speed $c > c_\beta$, perturbations $q$ obey $q_t = \mathcal{L} q$ with

$$\mathcal{L} q = \partial_z^2 \big( D(\hat u) q \big) + c\, \partial_z q + R'(\hat u)\, q .$$

Writing the eigenvalue problem $\mathcal{L} q = \Lambda q$ as a first-order system in $(q, s)$, $s = \partial_z(D(\hat u) q)$, and desingularising with $D(\hat u)\, d\xi = dz$ gives a regular (desingularised) operator $\tilde{\mathcal{T}}(\Lambda)$ on $\mathbb{R}$ whose far-field matrices are

$$A_\pm(\Lambda) = \begin{pmatrix} 0 & 1 \\ D_\pm (\Lambda - R'_\pm) & -c \end{pmatrix}, \qquad (D_+, R'_+) = (D_i, \lambda), \ (D_-, R'_-) = (D_g, -\lambda).$$

**Statement.** Items 1–4 concern the essential and absolute spectra of the desingularised operator $\tilde{\mathcal{T}}$, which are determined by $A_\pm(\Lambda)$.

1. The boundary of the unweighted essential spectrum (in $H^1(\mathbb{R})$) consists of the parabolas $\Lambda_\pm(k) = -D_\pm k^2 + ick + R'_\pm$, $k \in \mathbb{R}$. Since $\Lambda_+(0) = \lambda > 0$, every such wave is spectrally unstable in the unweighted space.
2. The absolute spectra are the half-lines

$$\sigma^+_{\mathrm{abs}} = \Big\{ \Lambda \in \mathbb{R} : \Lambda < \lambda - \frac{c^2}{4 D_i} \Big\}, \qquad \sigma^-_{\mathrm{abs}} = \Big\{ \Lambda \in \mathbb{R} : \Lambda < -\lambda - \frac{c^2}{4 D_g} \Big\}$$

(eqs. (35)-(36)). $\sigma^-_{\mathrm{abs}}$ always lies in the open left half-plane; $\sigma^+_{\mathrm{abs}}$ does so exactly when $c \ge c^*$; at $c = c^*$ its supremum is $0$.
3. For $c_\beta < c < c^*$ the waves are absolutely unstable: in every one-sided weighted space $H^1_\nu$ ($e^{\nu z} q \in H^1$) the essential spectrum still meets the open right half-plane.
4. For $c > c^*$, every weight $\nu$ in the open interval of eq. (37), which contains $\nu = c/(2D_i)$, moves the whole essential spectrum into the open left half-plane, at a positive distance from the imaginary axis; $\nu = c/(2D_i)$ moves its right edge furthest, to $\lambda - c^2/(4D_i) < 0$, the right end of $\sigma^+_{\mathrm{abs}}$.
5. At $c = c^*$ no weight moves the essential spectrum into the open left half-plane: for every $\nu$ the weighted spectrum meets the closed right half-plane, and the best weight $\nu = c^*/(2D_i)$ leaves its right edge at $0$ (marginal stability).

So the minimal speed $c^*$ of nonnegative monotone waves coincides with the onset of absolute instability, as for the Fisher-KPP equation: absolutely unstable below $c^*$, marginal at $c^*$, and strictly weighted-stable in essential spectrum above it. These statements do not settle the full spectrum of the original singular operator $\mathcal L$: possible contributions from the interior singularities of the wave, where $D(\hat u) = 0$, are left open in the source (Remark 3), and its numerical study (Section 4.4) counts real point eigenvalues only, not the entire point spectrum.

## Depends on

- [Smooth monotone travelling waves of a logistic equation with sign-changing aggregation diffusivity](negative-diffusion-logistic-travelling-waves.md)

## Expansion

The eigenvalues of $A_\pm(\Lambda)$ are $\mu = \tfrac12\big(-c \pm \sqrt{c^2 + 4D_\pm(\Lambda - R'_\pm)}\big)$. The essential-spectrum boundary is where one of them is purely imaginary, which gives the parabolas. The absolute spectrum is where the two have equal real part, i.e. the square root is purely imaginary, which gives the half-lines. Weighting by $e^{\nu z}$ adds $D_\pm \nu I$ to $A_\pm$, shifting the real-axis crossing of the $+\infty$ parabola to $K^\nu_+ = D_i \nu^2 - c\nu + \lambda$. This quadratic in $\nu$ has a negative value iff its discriminant $c^2 - 4\lambda D_i$ is positive, i.e. $c > c^*$, and its minimum, attained at $\nu = c/(2D_i)$, equals $\lambda - c^2/(4D_i)$; at $c = c^*$ this minimum is $0$, i.e. $K^\nu_+ = D_i(\nu - c/(2D_i))^2 \ge 0$ for every $\nu$, so the weighted spectrum always touches or crosses the imaginary axis. One checks $K^\nu_- < K^\nu_+$, so the $-\infty$ parabola does not obstruct.

## Sources

- Y. Li, P. van Heijster, R. Marangell and M. J. Simpson, Travelling wave solutions in a negative nonlinear diffusion-reaction model, *J. Math. Biol.* 81 (2020), 1495–1522, Section 3, <https://doi.org/10.1007/s00285-020-01547-1>, PMCID PMC7717045.
