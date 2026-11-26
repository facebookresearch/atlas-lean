# Proof of the Kuramoto conjecture for the continuum Kuramoto model

In the continuum limit of the Kuramoto model with natural-frequency density $g$ and coupling strength $K$, let $K_c = 2/(\pi g(0))$ and let $\eta(t)$ be the continuum order parameter, with the incoherent (de-synchronized) state $r \equiv 0$ as the trivial steady state. Chiba proves:

1. (Theorem 1.1) If $g$ is even, unimodal and continuous and $K > K_c$, the trivial state is linearly unstable; this linear instability was essentially obtained by Strogatz and Mirollo.
2. (Theorem 1.2) If $g$ is the Gaussian density or an even, unimodal rational function bounded on $\mathbb{R}$, and $0 < K < K_c$, there is $\delta > 0$ such that if the Fourier coefficients $\bigl|\int_0^{2\pi} e^{ij\theta} h(\theta)\, d\theta\bigr|$ of the initial condition are at most $\delta$ for $j = 1, 2, \dots$, then $\eta(t)$ decays to zero exponentially; the stability holds in the topology of a rigged Hilbert space.
3. (Theorem 1.3, nondegenerate case) For the same $g$, assume in addition $g''(0) < 0$. Then there is $\varepsilon_0 > 0$ such that for $K_c < K < K_c + \varepsilon_0$ the continuum model has a branch of partially synchronized steady states bifurcating from the incoherent state, whose order parameter has modulus

    $$r_\infty(K) = \sqrt{\frac{-16}{\pi K_c^4\, g''(0)}}\, \sqrt{K - K_c} + O(K - K_c),$$

    which is the bifurcation conjectured by Kuramoto. The hypothesis $g''(0) < 0$ is needed for the amplitude to be defined: the admissible rational density $g(\omega) = C/(1 + \omega^4)$ has $g''(0) = 0$. The convergence $r(t) \to r_\infty(K)$ as $t \to \infty$ is claimed only for initial conditions in a basin specified as part of the statement, not for every initial condition with small Fourier coefficients: the uniform initial phase density $h = 1/(2\pi)$, with any $g$, has all the specified Fourier coefficients zero, and its order parameter stays $r(t) = 0$ for all $t$, also above $K_c$. Chiba's printed Theorem 1.3 is worded for small initial conditions in general; this counterexample shows that at least the incoherent state must be excluded.

## Expansion

1. The model: the continuum Kuramoto equation for the density of oscillators over phases and frequencies, the order parameter, and the incoherent state.
2. Theorem 1.1: the linearized operator, its continuous spectrum on the imaginary axis, and the eigenvalue for $K > K_c$.
3. The rigged Hilbert space, the generalized spectral theory and the resonance poles, leading to the stability of Theorem 1.2 (Theorem 6.1 of the source).
4. The centre-manifold reduction on the rigged Hilbert space and the bifurcation of Theorem 1.3 with the amplitude formula for $g''(0) < 0$ (Theorem 7.10 of the source), followed by a separate basin statement: an explicit set of small initial conditions, excluding the incoherent state, from which $r(t) \to r_\infty(K)$.
5. For the Lorentzian $g$, the same picture from the Ott–Antonsen reduction of the continuum model, as a separate statement.

## Sources

- H. Chiba, A proof of the Kuramoto conjecture for a bifurcation structure of the infinite-dimensional Kuramoto model, Ergodic Theory Dynam. Systems 35 (2015), 762–834, Theorems 1.1–1.3. <https://arxiv.org/abs/1008.0249>
