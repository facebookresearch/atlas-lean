# Generalized linear chain trick for cyclic compartmental models

**Setting.** Consider the cyclic, possibly delayed, compartmental system

$$\frac{d}{dt}x_i(t)=f_i\Big(\int_0^\infty x_{i-1}(t-\phi)\,K_i(\phi)\,d\phi\Big)-\mu\big(x_n(t)\big)\,x_i(t),\qquad i=1,\dots,n\ (\text{indices mod } n),$$

where each $K_i$ is a probability density and the transit functions $f_i$ may be nonlinear. The removal rate $\mu$ is the same in every compartment and depends only on the last compartment. With $K_i=\delta_{\tau_i}$ this covers cyclic feedback systems with discrete delays (such as lac operon or Goodwin-type negative feedback loops). With $K_i=\delta_0$ it covers cyclic ODEs.

**Theorem.**

1. Along solutions, each intermediate compartment is a functional of the history of the previous one and of $x_n$:

$$x_i(t)=\int_0^\infty f_i\Big(\int_0^\infty x_{i-1}(t-s-\phi)K_i(\phi)\,d\phi\Big)\exp\Big(-\int_{t-s}^t\mu(x_n(u))\,du\Big)ds .$$

Iterating gives $x_i(t)=G_i(x_{n,t})$, a functional of the history segment $x_{n,t}$ of $x_n$ alone.
2. The system, with initial data $x_i(s)=\xi_i(s)$ for $s\le t_0$, is equivalent to the scalar distributed delay differential equation

$$\frac{d}{dt}x_n(t)=f_n\Big(\int_0^\infty G_{n-1}\big(x_n(t-\phi)\big)K_n(\phi)\,d\phi\Big)-\mu(x_n(t))\,x_n(t),$$

with a correspondingly constructed history function $\psi$ such that $\xi_i=G_i(\psi)$.
3. If $\mu\le\mu_{\max}$, $f_i(0)=0$, $f_i(x)>0$ for $x>0$, and the initial data are positive in the averaged sense, then $x_n(t)\ge0$ for all $t>0$.

## Proof sketch

When transit rates are constant and $\mu$ is constant, solving each linear stage by variation of constants and composing the gamma kernels gives the classical linear chain trick: a chain of exponential stages equals an Erlang-distributed delay. The generalization keeps nonlinear $f_i$ and state-dependent removal. Each stage is still linear in its own variable once the removal rate is known, so it can be solved explicitly as a functional of its input and of $x_n$. The cyclic structure closes the loop on a single variable. The scalar distributed DDE therefore carries all the dynamics, and stability or oscillation results for scalar delay equations transfer to multi-stage biological feedback loops. Conversely, a distributed DDE can be realized by a finite-dimensional system only for special kernels, so the equivalence is between phase spaces of different dimension.

## Sources

- Tyler Cassidy, "Distributed Delay Differential Equation Representations of Cyclic Differential Equations", *SIAM Journal on Applied Mathematics* 81 (2021), 1742–1766, <https://doi.org/10.1137/20m1351606>. Preprint version: arXiv:2007.03173 (2020), Section 2 (cyclic system, Lemma 2.1, Theorems 2.2–2.3 reduction to a scalar distributed DDE), Section 3 (non-negativity proposition), Section 4 (examples), <https://doi.org/10.48550/arXiv.2007.03173>.
