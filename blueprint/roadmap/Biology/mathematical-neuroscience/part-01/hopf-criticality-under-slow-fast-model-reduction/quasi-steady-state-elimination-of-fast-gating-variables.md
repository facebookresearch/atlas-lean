# Quasi-steady-state elimination of fast gating variables

**Setting.** A dimensionless physiological model in slow-fast form

$$v'=f(v,m,n,\mu,\varepsilon),\qquad m'=h(v,m,n,\mu,\varepsilon),\qquad n'=\varepsilon\,g(v,m,n,\mu,\varepsilon),$$

has fast variables $(v,m)\in\mathbb R\times\mathbb R^j$ (voltage or cytosolic calcium $v$, fast gates $m$), slow variables $n\in\mathbb R^l$, parameters $\mu$ and $0<\varepsilon\ll1$. Its critical manifold is $S_0=\{f=h=0\}$ at $\varepsilon=0$, and $J=\begin{bmatrix}\partial_vf&D_mf\\\partial_vh&D_mh\end{bmatrix}$ is the layer-problem Jacobian on $S_0$. The quasi-steady-state reduction replaces the gates by the solution $m=M(v,n,\mu,\varepsilon)$ of $h=0$ (in neural models $m_i=m_{i,\infty}(v)$).

**Proposition (normally hyperbolic case).** If every eigenvalue of $J$ has nonzero real part along $S_0$, there is an $l$-dimensional invariant slow manifold $S_\varepsilon$, a smooth $O(\varepsilon)$ perturbation of $S_0$ given as a graph $(v,m)=(\hat V(n,\mu,\varepsilon),\hat M(n,\mu,\varepsilon))$, and the slow flow $\dot n=g(\hat V,\hat M,n,\mu,\varepsilon)$ on it is a regular $O(\varepsilon)$ perturbation of the reduced flow on $S_0$. If all eigenvalues have negative real part, eliminating $v$ and $m$ by their quasi-steady states is correct to leading order after a transient.

**Proposition (fold case).** Suppose $J$ has a simple zero eigenvalue on an $(l-1)$-dimensional fold set $F\subset S_0$ (rank $j=k-1$, the other eigenvalues with negative real parts, generic fold non-degeneracy conditions) and $D_mh$ is invertible. Then near $F$ there is an $(l+1)$-dimensional centre manifold $W^c$ given as a graph $m=\hat M(v,n,\mu,\varepsilon)$, and the dynamics reduces to

$$v'=f(v,\hat M,n,\mu,\varepsilon),\qquad n'=\varepsilon\,g(v,\hat M,n,\mu,\varepsilon).$$

In general $\hat M\ne M$; the two agree on the critical manifold as $\varepsilon\to0$, so the quasi-steady-state reduction near a fold is qualitatively but not quantitatively faithful.

## Depends on

- [The Hodgkin–Huxley vector field](../../hodgkin-huxley-model/field.md)

## Expansion

The first case is Fenichel's persistence theorem. In the fold case, invertibility of $D_mh$ makes $\det J=\det(D_mh)\,(\partial_vf-D_mf(D_mh)^{-1}\partial_vh)$, so the zero eigenvalue lives in the $v$-direction and the one-dimensional centre direction of the layer problem is a graph over $v$; the change of variables $\hat m=m-\hat M$ aligns the centre manifold with $\hat m=0$. Rinzel's reduction of the Hodgkin–Huxley model, which sets the sodium activation gate to $m_\infty(V)$, is of this type.

## Sources

- W. Zhang, V. Kirk, J. Sneyd, M. Wechselberger, "Changes in the criticality of Hopf bifurcations due to certain model reduction techniques in systems with multiple timescales", Journal of Mathematical Neuroscience 1 (2011) 9, Section 2 and Section 2.1: Assumptions 1 and 2, Propositions 1 and 2, Equations (3)–(9), <https://doi.org/10.1186/2190-8567-1-9>, PMCID PMC3520151.
