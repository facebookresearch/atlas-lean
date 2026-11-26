# Detailed balance excludes heteroclinic cycles in Wilson–Cowan networks

**Model.** The spatially discrete Wilson–Cowan/Amari firing-rate system for $n$ neuronal populations is
$$\dot x=-x+\sigma(Wx+b),\qquad x\in\mathbb R^n,$$
with connectivity $W$, positive inputs $b$, and a smooth strictly increasing activation $\sigma:\mathbb R\to(-\alpha,\beta)$ applied componentwise. $W$ satisfies *detailed balance* if there are $\tau_i>0$ with $\tau_iW_{ij}=\tau_jW_{ji}$, i.e. $TW$ is symmetric for $T=\mathrm{diag}(\tau)$.

**Theorem (Lyapunov function).** Under detailed balance,
$$V(x)=\sum_{i=1}^n\tau_i\int_0^{x_i}\sigma^{-1}(s)\,ds-\tfrac12x^\top TWx-x^\top Tb$$
is a strict Lyapunov function on $(-\alpha,\beta)^n$, so the network has no heteroclinic cycles and no nonconstant periodic orbits; this persists for small perturbations of $W$ outside a neighbourhood of the equilibria.

**Theorem (prescribed sequential states).** Suppose $W$ is designed so that $n$ linearly independent activity patterns $\bar x_1,\dots,\bar x_n$ are equilibria, each with entries in $\{0,a_i\}$ for some $a_i\in(-\alpha,\beta)\setminus\{0\}$, and the vector $u^\top=\mathbf 1^\top\bar X^{-1}$ is positive. Then $W$ automatically satisfies detailed balance, so the network cannot cycle through these states. If moreover $\sigma'(s)<\sigma(s)/s<\sigma'(0)$ for $s\ne0$, each $\bar x_i$ has real Jacobian spectrum with at least $|S_i|$ stable and $n-|S_i|-1$ unstable directions, where $S_i$ is the active set of $\bar x_i$.

**Contrast.** Without detailed balance cycling occurs: for $n=3$, uniform input and cyclic inhibition $W_{21}=W_{32}=W_{13}=-c$, every trajectory off the diagonal converges to a nonconstant periodic orbit once $c$ exceeds a threshold.

**Lifting.** Heteroclinic sequences can instead be realized at the population level by approximating a Lotka–Volterra-type field $g$ with $f(x)=-x+P\sigma(Wx+b)$ ($C^1$ universal approximation); the lifted system $\dot y=-y+\sigma(WPy+b)$ has, for each $T$-periodic orbit $x_*$ of $f$, a unique $T$-periodic orbit $y_*$ with $Py_*=x_*$, attracting its fibre at rate $e^{-t}$.

## Expansion

Along solutions, $\dot V=-\sum_i\tau_i\bigl(\sigma^{-1}(x_i)-(Wx+b)_i\bigr)\bigl(x_i-\sigma((Wx+b)_i)\bigr)\le0$, with equality only at equilibria, because $\sigma^{-1}$ is increasing; detailed balance is what makes $V$ the potential of the vector field in the $T$-weighted metric. A gradient-like system cannot return to where it started, which rules out cycles. For the prescribed binary-level states, the connectivity is determined by the patterns, and positivity of $u$ supplies the weights $\tau_i$ that symmetrize it.

## Sources

- M Virginia Bolelli, Luca Greco and Dario Prandi, "Modeling sequential cognitive states via population level cortical dynamics", arXiv:2605.02365 (2026), Section 3 (Proposition 3.1, Theorems 3.3, 3.5, 3.7, 3.11 and 3.12, Corollary 3.13) and Section 4 (Corollary 4.2, Proposition 4.3), <https://doi.org/10.48550/arXiv.2605.02365>.
