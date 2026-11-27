# Random Fourier features

Random features replace a shift-invariant kernel $k(x, y) = k(x - y)$ by an explicit low-dimensional feature map whose inner products approximate it (Rahimi and Recht 2007). By [Bochner's theorem](../../../../Probability/characteristic-functions/bochner-s-theorem/README.md), a continuous positive-definite shift-invariant kernel, properly scaled, is the characteristic function of a probability measure $p$ on frequencies. With $\omega \sim p$ and a phase $b$ uniform on $[0, 2\pi]$, the feature $z_{\omega, b}(x) = \sqrt{2} \cos(\langle \omega, x\rangle + b)$ satisfies $\mathbb{E}[z_{\omega, b}(x) z_{\omega, b}(y)] = \operatorname{Re} \varphi_p(x - y)$, which is $k(x - y)$ when $k$ is real; averaging $D$ independent features gives a $D$-dimensional map whose inner products concentrate around the kernel at each pair of points, with the tail bound $2e^{-D\varepsilon^2/8}$ (the source states the sharper $2e^{-D\varepsilon^2/4}$). Rahimi and Recht also prove uniform convergence over a compact set (their Claim 1).

- [Random Fourier feature](fourier-feature.md)
- [Uniform phase](phase-measure.md)
- [Averaging a random Fourier feature over the phase](phase-average-fourier-feature-mul.md)
- [Random Fourier features are unbiased](integral-fourier-feature-mul.md)
- [Averaging $D$ random Fourier features is unbiased](integral-avg-fourier-feature-mul.md)
- [Concentration of random Fourier features at a pair of points](measure-real-abs-avg-fourier-feature-mul.md)

## Related topics

- [Positive-definite kernels](../../../../Analysis/hilbert-spaces/positive-definite-kernels/README.md): the kernels approximated, and their feature maps; random features are a finite-dimensional, randomized feature map.
- [Kernel ridge regression and GBLUP](../kernel-ridge-regression-and-gblup/README.md): a kernel machine that random features approximate by a linear one in the random feature space.
- [Bochner's theorem](../../../../Probability/characteristic-functions/bochner-s-theorem/README.md): the Fourier representation of shift-invariant positive-definite kernels by probability measures.
