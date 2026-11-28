# Periodic solutions of a scalar impulsive differential equation

**Setting.** Consider the autonomous scalar impulsive differential equation with impulses at fixed times and linear impulse maps,

$$\frac{dX}{dt} = g(X), \quad t \ne \tau_k, \qquad X(\tau_k^+) = (1+\alpha_k)\,X(\tau_k^-), \qquad X(0) = X_0 \in U,$$

with $g$ locally Lipschitz on an interval $U$, and assume periodic impulses $\tau_k = k\omega$ ($\omega > 0$) of constant size $\alpha_k = \alpha > -1$. The solution is right-continuous, absolutely continuous between impulses, and unique; every bounded solution converges to a periodic one, and a non-constant periodic solution has minimal period $\omega$. Let $\varphi_\omega(X_0)$ be the time-$\omega$ flow of $X' = g(X)$ without impulses (a strictly increasing bijection of $U$) and

$$\Gamma_\omega(X_0) = \frac{X_0}{\varphi_\omega(X_0)} - 1 \qquad (\varphi_\omega(X_0) \ne 0).$$

**Proposition (periodicity criterion).** For $X_0$ with $\varphi_\omega(X_0) \ne 0$, the solution $X(\cdot\,;X_0,\alpha)$ is periodic if and only if

$$\alpha = \Gamma_\omega(X_0),$$

i.e. the impulse exactly undoes the drift over one period: $(1+\alpha)\varphi_\omega(X_0) = X_0$. If $\varphi_\omega(X_0) = 0$, the solution is identically $0$ when $g(0) = 0$ and is never periodic when $g(0) \ne 0$.

**Lemma (convergence).** Let $\gamma_{\omega,\alpha}(x) = (1+\alpha)\varphi_\omega(x) - x$, so that $X(k\omega)$ is the orbit of the increasing map $x \mapsto (1+\alpha)\varphi_\omega(x)$. If $\gamma_{\omega,\alpha}(X_0) > 0$, the solution converges to the periodic solution started at the smallest zero of $\gamma_{\omega,\alpha}$ above $X_0$, or diverges to $+\infty$ if there is none; symmetrically for $\gamma_{\omega,\alpha}(X_0) < 0$. Consequently the periodic solution through $X_*$ with $\Gamma_\omega(X_*) = \alpha$ is attractive or repulsive according to the sign changes of $\Gamma_\omega - \alpha$ at $X_*$.

**Theorem (convexity of the flow).** Let $X' = h(X)$ with $h$ continuously differentiable on $[a,b]$, positive on $[a,b)$ and $h(b) = 0$, and let $\varphi_\omega$ be its time-$\omega$ flow. For $X_0 \in (a,b)$, if $h'(\varphi_\omega(X_0)) - h'(X_0) > 0$ (resp. $< 0$), then $\varphi_\omega$ is convex (resp. concave) on a neighborhood of $X_0$. (Indeed $\varphi_\omega'(X_0) = h(\varphi_\omega(X_0))/h(X_0)$, whose derivative has the sign of $h'(\varphi_\omega(X_0)) - h'(X_0)$.)

## Expansion

Between impulses the solution follows the flow, and the impulse multiplies by $1+\alpha$, so $X(k\omega) = \big((1+\alpha)\varphi_\omega\big)^{k}(X_0)$. An increasing one-dimensional map has only monotone orbits, which converge to the nearest fixed point in the direction of motion; fixed points are the solutions of $\Gamma_\omega(X_0) = \alpha$. The number and stability of periodic solutions therefore reduce to the level sets of the single function $\Gamma_\omega$, whose shape is controlled by the convexity of $\varphi_\omega$. Convexity is proved by approximating $g$ with piecewise-affine functions, for which the flow is explicit (piecewise exponential), and comparing the exponential rates at the start and end of the trajectory.

## Sources

- Simon Girel and Fabien Crauste, "Existence and stability of periodic solutions of an impulsive differential equation and application to CD8 T-cell differentiation", arXiv:1803.01674 (2018), Section 2 (Definition 1, Propositions 1–3, Lemma 2), Section 3 (Proposition 4, Lemma 3, Definition 3) and Section 4 (Lemmas 4–7, Propositions 5–6, Theorem 1), <https://doi.org/10.48550/arXiv.1803.01674>. Published version: Journal of Mathematical Biology, Springer Verlag (Germany), 2018, pp.1-32.
