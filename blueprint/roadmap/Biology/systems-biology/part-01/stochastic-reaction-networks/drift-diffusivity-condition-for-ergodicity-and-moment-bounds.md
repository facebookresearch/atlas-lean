# Drift–diffusivity condition for ergodicity and moment bounds

**Setting.** A stochastic reaction network with $d$ species and reactions $k = 1, \dots, K$ is a continuous-time Markov chain $X(t)$ on an irreducible state space $\mathcal{E} \subseteq \mathbb{Z}^d_{\ge 0}$; reaction $k$ fires at rate (propensity) $\lambda_k(x)$ and changes the state by its stoichiometric vector $\zeta_k \in \mathbb{Z}^d$.

**Condition DD (drift–diffusivity).** There are a vector $v \in \mathbb{R}^d_{>0}$ and constants $c_1, c_2 > 0$, $c_3, c_4 \ge 0$ such that, for all $x \in \mathcal{E}$,

$$\text{(DD1)}\quad \sum_{k} \lambda_k(x)\,\langle v, \zeta_k\rangle \le c_1 - c_2 \langle v, x\rangle, \qquad \text{(DD2)}\quad \sum_k \lambda_k(x)\,\langle v, \zeta_k\rangle^2 \le c_3 + c_4 \langle v, x\rangle .$$

DD1 bounds the drift and DD2 the diffusion of the scalar process $\langle v, X(t)\rangle$, measured in the weighted $\ell_1$ norm $\|x\|_v = \langle v, x\rangle$ on the nonnegative orthant.

**Results.** Under Condition DD:

1. *Uniform moment bounds:* for every $m \ge 1$ and initial state $x_0$, $\sup_{t \ge 0} \mathbb{E}\,\langle v, X(t)\rangle^m < \infty$, with explicit constants, and $\limsup_{t\to\infty}\mathbb{E}\,\langle v, X(t)\rangle^m$ is bounded by a constant independent of $x_0$. Hence the family of distributions of $X(t)$ is tight.
2. *Ergodicity:* the process is exponentially ergodic: it has a unique stationary distribution $\pi$, the distribution of $X(t)$ converges to $\pi$ from any initial state, and time averages along a single trajectory converge to $\pi$-expectations.
3. *Moment convergence:* every moment of $X(t)$ converges to the corresponding (finite) moment of $\pi$.
4. *Light tails:* for some $\epsilon > 0$, $\sup_{t}\mathbb{E}\, e^{\epsilon\langle v, X(t)\rangle} < \infty$ and $\mathbb{E}_\pi e^{\epsilon\langle v, X\rangle} < \infty$.

**Unimolecular networks.** If every reaction has at most one reactant molecule, propensities are affine: $\sum_k \lambda_k(x)\zeta_k = A x + b$ with $A$ Metzler. If $A$ is Hurwitz, there is $v > 0$ with $v^{\top} A < 0$ componentwise (found by a linear program), and then DD1 holds with $c_2 = \min_i (-v^\top A)_i / v_i$, while DD2 holds automatically because the left side is affine in $x$; so an irreducible unimolecular network with Hurwitz $A$ is ergodic with all moments converging. Checking that $A$ is Hurwitz for all rate values in a box gives robust (structural) ergodicity.

## Depends on

- [Non-explosivity of complex-balanced stochastic reaction networks](non-explosivity-of-complex-balanced-stochastic-reaction-networks.md)

## Expansion

DD1 is a Foster–Lyapunov drift condition for the linear function $V(x) = \langle v, x\rangle$: outside a finite set the generator gives $\mathcal{L}V \le -\tfrac{c_2}{2} V$, which yields positive recurrence and exponential ergodicity of an irreducible chain (Meyn–Tweedie). Moment bounds follow by applying the generator to $V^m$: expanding $(V + \langle v, \zeta_k\rangle)^m - V^m$, the leading term is $m V^{m-1}$ times the drift, controlled by DD1, the next is controlled by DD2, and the remaining terms are of lower order in $V$, so $\frac{d}{dt}\mathbb{E}V^m \le C - c\,\mathbb{E}V^m$ for constants $C, c > 0$, and Grönwall gives uniform bounds. Exponential moments follow from the same computation for $e^{\epsilon V}$ with $\epsilon$ small. The approach reduces questions about infinite-dimensional chemical master equations to finite-dimensional linear algebra and optimization: find one positive vector $v$.

## Sources

- A. Gupta, C. Briat, M. Khammash, "A scalable computational framework for establishing long-term behavior of stochastic reaction networks", PLoS Computational Biology 10 (2014) e1003669, Results (Condition 1 / Condition DD, Theorems 2, 3, 5, 6, Proposition 4; unimolecular networks, Propositions 7–8), <https://doi.org/10.1371/journal.pcbi.1003669>.
