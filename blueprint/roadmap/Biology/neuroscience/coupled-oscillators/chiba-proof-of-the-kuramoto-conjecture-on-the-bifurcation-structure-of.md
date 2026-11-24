# Proof of the Kuramoto conjecture for the continuum Kuramoto model

In the continuum limit of the Kuramoto model with natural-frequency density $g$ and coupling strength $K$, let $K_c = 2/(\pi g(0))$ and let $\eta(t)$ be the continuum order parameter, with the incoherent (de-synchronized) state $r \equiv 0$ as the trivial steady state. Chiba proves:

1. (Theorem 1.1) If $g$ is even, unimodal and continuous and $K > K_c$, the trivial state is linearly unstable; this linear instability was essentially obtained by Strogatz and Mirollo.
2. (Theorem 1.2) If $g$ is the Gaussian density or an even, unimodal rational function bounded on $\mathbb{R}$, and $0 < K < K_c$, there is $\delta > 0$ such that if the Fourier coefficients $\bigl|\int_0^{2\pi} e^{ij\theta} h(\theta)\, d\theta\bigr|$ of the initial condition are at most $\delta$ for $j = 1, 2, \dots$, then $\eta(t)$ decays to zero exponentially; the stability holds in the topology of a rigged Hilbert space.
3. (Theorem 1.3) For the same $g$ there are $\varepsilon_0, \delta > 0$ such that if $K_c < K < K_c + \varepsilon_0$ and the initial Fourier coefficients are smaller than $\delta$, then
$$r(t) = |\eta(t)| \to \sqrt{\frac{-16}{\pi K_c^4\, g''(0)}}\, \sqrt{K - K_c} + O(K - K_c), \qquad t \to \infty,$$
which is the bifurcation conjectured by Kuramoto.

## Expansion

1. The model: the continuum Kuramoto equation for the density of oscillators over phases and frequencies, the order parameter, and the incoherent state.
2. Theorem 1.1: the linearized operator, its continuous spectrum on the imaginary axis, and the eigenvalue for $K > K_c$.
3. The rigged Hilbert space, the generalized spectral theory and the resonance poles, leading to the stability of Theorem 1.2 (Theorem 6.1 of the source).
4. The centre-manifold reduction on the rigged Hilbert space and the bifurcation of Theorem 1.3 with the amplitude formula (Theorem 7.10 of the source).
5. For the Lorentzian $g$, the same picture from the Ott–Antonsen reduction of the continuum model, as a separate statement.

## Sources

- H. Chiba, A proof of the Kuramoto conjecture for a bifurcation structure of the infinite-dimensional Kuramoto model, Ergodic Theory Dynam. Systems 35 (2015), 762–834, Theorems 1.1–1.3. <https://arxiv.org/abs/1008.0249>
