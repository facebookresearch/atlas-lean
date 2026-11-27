# Linear-programming bounds on stationary averages of the chemical master equation

Let $Q$ be the totally stable, conservative rate matrix of a stochastic reaction network on a countable state space $\mathcal{S}$, and $\mathcal{P}$ the set of stationary solutions of the chemical master equation ($\pi Q = 0$, $\pi \ge 0$, $\pi(\mathcal{S}) = 1$). Let $w : \mathcal{S} \to [0,\infty)$ be norm-like (finite sublevel sets $\mathcal{S}_r = \{w < r\}$).

**Assumption 13.** $\mathcal{P} \ne \emptyset$ and every $\pi \in \mathcal{P}$ satisfies the moment bound $\langle w\rangle_\pi \le c$ for a known constant $c$ (for rational propensities, computable by the semidefinite moment bounds).

Then $\pi(\mathcal{S}_r^c) \le c/r =: \varepsilon_r$. Let $\mathcal{N}_r = \{x \in \mathcal{S}_r : q(z,x) = 0\ \forall z \notin \mathcal{S}_r\}$ and define the finite-dimensional polytope

$$\mathcal{P}^r = \Big\{\pi^r : \pi^r Q(x) = 0\ (x \in \mathcal{N}_r),\ \ \pi^r(\mathcal{S}_r^c) = 0,\ \ \pi^r \ge 0,\ \ 1 - \varepsilon_r \le \pi^r(\mathcal{S}) \le 1,\ \ \langle w\rangle_{\pi^r} \le c\Big\}.$$

**Lemma 14.** If $\pi \in \mathcal{P}$, its restriction $\pi_{|r}$ to $\mathcal{S}_r$ lies in $\mathcal{P}^r$.

**Theorem 15.** Under Assumption 13, for $\pi \in \mathcal{P}$ and any $f : \mathcal{S} \to \mathbb{R}$, with the linear programs $l_f^r = \inf\{\langle f\rangle_{\pi^r} : \pi^r \in \mathcal{P}^r\}$ and $u_f^r = \sup\{\langle f\rangle_{\pi^r} : \pi^r \in \mathcal{P}^r\}$, one has $l_f^r \le \langle f\rangle_{\pi_{|r}} \le u_f^r$ for all $r$, and:

1. if $f \ge 0$ off $\mathcal{S}_r$, then $l_f^r \le \langle f\rangle_\pi$; if $f \le 0$ off $\mathcal{S}_r$, then $\langle f\rangle_\pi \le u_f^r$;
2. if $f$ is $\pi$-integrable, $\ l_f^r - c\sup_{x\notin\mathcal{S}_r}\frac{|f(x)|}{w(x)} \le \langle f\rangle_\pi \le u_f^r + c\sup_{x\notin\mathcal{S}_r}\frac{|f(x)|}{w(x)}$;
3. if $\sup_{x\notin\mathcal{S}_r}|f(x)|/w(x) \to 0$ as $r \to \infty$, then $f$ is $\pi$-integrable for all $\pi \in \mathcal{P}$ and $l_f^r \to \inf_{\pi\in\mathcal{P}}\langle f\rangle_\pi$, $u_f^r \to \sup_{\pi\in\mathcal{P}}\langle f\rangle_\pi$.

**Corollary 17.** If moreover $\mathcal{P} = \{\pi\}$, then $l_f^r$ and $u_f^r$ both converge to $\langle f\rangle_\pi$, and any feasible sequence $\pi^r \in \mathcal{P}^r$ converges to $\pi$ in the weak$^*$ sense.

Choosing $f = 1_x$ bounds individual stationary probabilities, so the method produces computable two-sided error bars on truncation-based approximations of the stationary distribution, e.g. for toggle switches and bursty gene expression.

## Depends on

- [Semidefinite-programming bounds on stationary moments of the chemical master equation](sdp-moment-bounds-for-rational-propensity-cmes.md)

## Expansion

The only stationary equations kept are those at states in $\mathcal{N}_r$, which cannot be entered from outside the truncation and therefore involve only probabilities inside $\mathcal{S}_r$; the restriction of any true stationary solution satisfies them exactly, while Markov's inequality with the moment bound controls the missing tail mass. Hence $\mathcal{P}^r$ is an outer approximation and optimizing a linear functional over it brackets the truncated average. The tail error $\sum_{x\notin\mathcal{S}_r}|f|\pi \le \sup_{x\notin\mathcal{S}_r}(|f|/w)\,c$ gives item 2. Convergence uses compactness (tightness from the uniform moment bound): limit points of optimizers are stationary solutions, so the bounds approach the extremes of $\langle f\rangle$ over $\mathcal{P}$, and to the single value when the solution is unique.

## Sources

- Juan Kuntz, Philipp Thomas, Guy-Bart Stan and Mauricio Barahona, "Bounding the stationary distributions of the chemical master equation via mathematical programming", The Journal of Chemical Physics 151 (2019), 034109, <https://doi.org/10.1063/1.5100670>; numbering as in arXiv:1702.05468: Lemmas 3, 5, 14, Corollaries 6, 17 and Theorem 15.
