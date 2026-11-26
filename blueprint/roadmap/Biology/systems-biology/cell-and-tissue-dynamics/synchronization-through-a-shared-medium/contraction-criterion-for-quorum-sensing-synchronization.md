# Contraction criterion for quorum-sensing synchronization

**Contraction.** A system $\dot x = f(x,t)$ on $\mathbb{R}^m$ is *contracting* if any two trajectories converge to each other exponentially. A sufficient condition is that for some constant invertible $\Theta$ the generalized Jacobian $F = \Theta\,\frac{\partial f}{\partial x}\,\Theta^{-1}$ satisfies $\mu(F(x,t)) \le -\lambda < 0$ for all $x$ and $t \ge 0$, where $\mu$ is a matrix measure (logarithmic norm) induced by a vector norm.

**Network.** $N$ nodes (e.g. bacteria) with states $x_i \in \mathbb{R}^n$ do not interact directly but through a shared medium $z \in \mathbb{R}^d$ (e.g. the concentration of an autoinducer), which has its own dynamics:

$$\dot x_i = f(x_i, z, t), \quad i = 1,\dots,N, \qquad \dot z = g\big(z, \Psi(x_1,\dots,x_N), t\big).$$

**Theorem.**
1. (Homogeneous nodes) If $x \mapsto f(x, v(t), t)$ is contracting for every input $v(t) \in \mathbb{R}^d$ (uniformly), then all node trajectories converge globally exponentially towards each other, $|x_i(t) - x_j(t)| \to 0$, whatever the medium dynamics $g$ and coupling $\Psi$.
2. (Heterogeneous nodes) If nodes of type $\gamma(i)$ follow $\dot x_i = f_{\gamma(i)}(x_i,z,t)$ with each $f_\gamma(\cdot,v(t),t)$ contracting for every input, the network achieves *concurrent synchronization*: nodes of the same type converge to each other.
3. (Groups with local media) If nodes in groups $p$ also share group-level media $z_p$ with dynamics $g_p(z_p, v(t), t)$, concurrent synchronization holds when nodes of the same group are input-equivalent, all $f_p(\cdot, v, t)$ and $g_p(\cdot, v, t)$ are contracting for every input $v$, and $\partial f_p / \partial z_p$ are uniformly bounded.

## Expansion

The proof uses partial contraction: the virtual system $\dot y = f(y, z(t), t)$, with the actual medium trajectory $z(t)$ treated as an exogenous input, is contracting in $y$ and has every $x_i(t)$ as a particular solution. Contraction makes all its solutions converge exponentially to one another, so all $x_i$ do, without needing any property of $z$ beyond existence. The criterion therefore separates node dynamics from the possibly slow or nonlinear dynamics of the shared environment, which is what distinguishes quorum sensing from diffusive all-to-all coupling. Applications include synthetic gene oscillators coupled through a diffusing signalling molecule.

## Sources

- Giovanni Russo and Jean-Jacques E. Slotine, "Global convergence of quorum-sensing networks", arXiv:1003.5704 (2010), Section 2, Theorems 1-3, and Section 3, Theorems 4-6, <https://doi.org/10.48550/arXiv.1003.5704>.
