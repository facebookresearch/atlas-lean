# Wavelet scattering transform

The scattering transform (S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398, arXiv:1101.2286) builds representations of $L^2(\mathbb{R}^d)$ that are approximately translation invariant at the averaging scale $2^J$ and translation invariant in the limit $J \to \infty$, and that, unlike the Fourier modulus, are Lipschitz continuous to small deformations. One layer computes a low-pass average $A_J f = f \star \varphi_{2^J}$ and the moduli of wavelet coefficients $U[\lambda] f = |f \star \psi_\lambda|$; along a path $p = (\lambda_1, \dots, \lambda_m)$ the [scattering propagator](propagator.md) is the cascade $U[p] f = |\,|f \star \psi_{\lambda_1}| \star \psi_{\lambda_2}| \cdots \star \psi_{\lambda_m}|$, and the [windowed scattering](windowed-scattering.md) is $S_J[p] f = U[p] f \star \varphi_{2^J}$. The cascade is a convolutional network with fixed wavelet filters and modulus nonlinearities.

Two properties of a single layer, nonexpansiveness and norm preservation (which the Littlewood–Paley condition and the contraction $||a| - |b|| \le |a - b|$ give), already imply that the whole cascade is [nonexpansive](tsum-edist-sq-le.md) and satisfies the [energy identity](sum-enorm-sq-eq.md) $\|f\|^2 = \sum_{|p| < m} \|S_J[p] f\|^2 + \sum_{|p| = m} \|U[p] f\|^2$ at every depth; so the scattering preserves the norm [exactly when](tsum-enorm-sq-eq-iff-tendsto.md) the energy propagated to depth $m$ vanishes as $m \to \infty$. These structural results hold for an arbitrary layer. Mallat's analytic theorems are stated in dimension one for real signals: for [admissible wavelets](is-admissible.md) the propagated energy does vanish, so the scattering [preserves energy](tsum-lintegral-windowed-scattering-eq.md) (Theorem 2.6), and it is [Lipschitz continuous to $C^2$ deformations](windowed-scattering-lipschitz-deformatio.md) (Theorem 2.12).

- [Scattering propagator](propagator.md)
- [Sums over paths split along the first index](tsum-paths-succ.md)
- [Cascade inequality](cascade-le.md)
- [Cascade identity](cascade-eq.md)
- [Nonexpansiveness of a scattering cascade at every depth](sum-edist-sq-le.md)
- [The windowed scattering transform is nonexpansive](tsum-edist-sq-le.md)
- [Energy identity of a scattering cascade](sum-enorm-sq-eq.md)
- [Norm preservation is equivalent to the decay of the propagated energy](tsum-enorm-sq-eq-iff-tendsto.md)
- [Fourier transform in angular frequency](angular-fourier.md)
- [Dilated wavelet](dilate.md)
- [Low-pass window at scale $2^J$](low-pass.md)
- [Wavelet modulus operator](modulus-layer.md)
- [Windowed scattering transform](windowed-scattering.md)
- [Scattering wavelet in dimension one](is-scattering-wavelet.md)
- [The function $\hat\Psi$ of the admissibility condition](admissibility-function.md)
- [Admissible scattering wavelet in dimension one](is-admissible.md)
- [Energy conservation of the windowed scattering transform](tsum-lintegral-windowed-scattering-eq.md)
- [Lipschitz continuity of the windowed scattering transform to deformations](windowed-scattering-lipschitz-deformatio.md)

## Related topics

- [Conjugate mirror filters](../conjugate-mirror-filters/README.md): a wavelet basis subsamples the wavelet transform and is not translation invariant; the scattering uses the redundant, unsubsampled Littlewood–Paley wavelet transform and recovers translation invariance, approximately at the scale $2^J$ and exactly in the limit $J \to \infty$, by averaging moduli.
- [Fourier transform and uncertainty principles](../../fourier-transform/README.md): the Fourier modulus is translation invariant but unstable to dilations at high frequencies, the instability that grouping frequencies into dyadic wavelet bands removes.
- [Frames in Hilbert spaces](../../../hilbert-spaces/frames-in-hilbert-spaces/README.md): the Littlewood–Paley condition makes the unsubsampled wavelet transform an isometry, a continuous analogue of a tight frame with bound $1$; this is the norm preservation of one scattering layer.
