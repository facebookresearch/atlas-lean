# Well-posedness and stability of stochastic jump kinetics

**Setting.** A reaction network on $D$ species has $R$ reactions; reaction $r$ fires at propensity $w_r(x) \ge 0$ in state $x \in \mathbb{Z}_+^D$ and changes the state by $-\mathbb{N}_r$, where $\mathbb{N} \in \mathbb{Z}^{D \times R}$ is the stoichiometric matrix (sign convention as in the source). The copy-number process $X_t$ is the solution of the jump SDE driven by a Poisson random measure with state-dependent thinning,

$$dX_t = -\int \mathbb{N}\, \hat w(X_{t-}; z)\, \mu(dt \times dz),$$

which is the pathwise version of the chemical master equation; write $F(x) = -\mathbb{N} w(x)$ for the drift of the reaction-rate ODE $\dot x = F(x)$. Fix a weight vector $l > 0$ with $\min_i l_i = 1$ and $\|x\|_l = l^{\mathsf T} x$.

**Assumptions.** For $x, y \in \mathbb{Z}_+^D$, with $A, B, \beta_1, L > 0$, $\beta_2 \ge 0$ and $\alpha, M, \mu$ of any sign:

1. *(bounded growth)* $-l^{\mathsf T}\mathbb{N} w(x) \le A + \alpha \|x\|_l$;
2. *(absolutely bounded growth)* $(-l^{\mathsf T}\mathbb{N})^2 w(x)/2 \le B + \beta_1 \|x\|_l + \beta_2\|x\|_l^2$ (square taken entrywise);
3. *(local Lipschitz)* $(\mathbf{1}^{\mathsf T}\mathbb{N}^2)\,|w(x) - w(y)| \le L(1 + \|x + y\|_1)\|x - y\|$;
4. *(one-sided Lipschitz)* $(x - y, F(x) - F(y)) \le (M + \mu\|x+y\|_1)\|x - y\|^2$.

**Theorem.**

1. *(Moments.)* Under 1–2, for every integer $p \ge 1$, $\mathbb{E}\|X_t\|_l^p \le (\|X_0\|_l^p + 1)e^{Ct} - 1$ with $C$ depending on the constants and $p$; under 1 alone, $\mathbb{E}\|X_t\|_l \le \|X_0\|_l e^{\alpha_+ t} + A(e^{\alpha_+ t} - 1)/\alpha_+$ with $\alpha_+ = \alpha \vee 0$.
2. *(Existence.)* Under 1–2 with $\beta_2 = 0$, if $\|X_0\|_l^p$ is integrable then the solution has $p$ finite moments on bounded time intervals; if $\beta_2 > 0$ the same holds when $\|X_0\|_l^{p+1}$ is integrable.
3. *(Uniqueness.)* Under 1–4, two coupled paths with the same initial state coincide.
4. *(Ergodic moment bound.)* Under 1–2, if $\alpha + \beta_2(p - 1) \le -\kappa_p < 0$ then $\mathbb{E}\|X_t\|_l^p$ stays bounded as $t \to \infty$.
5. *(Continuity in the propensities.)* If the propensities of a coupled process $Y_t$ with the same initial state are perturbed by $\delta$, then $\mathbb{E}\sup_{s \le t}\|X_s - Y_s\|^2 \to 0$ as $\delta \to 0^+$; for bounded processes $\mathbb{E}\|X_t - Y_t\|^2 \le \delta(e^{Ct} - 1)$.

For elementary reactions the constants are explicit: linear propensities $w_r = q_r^{\mathsf T}x$ give $M$ equal to the Euclidean logarithmic norm of $-\mathbb{N}Q^{\mathsf T}$, and a quadratic propensity $w_r = x^{\mathsf T}Sx$ gives $M = 0$ and $\mu \le \|\mathbb{N}_r\|\,\|S\|$.

## Expansion

Polynomial propensities are not globally Lipschitz, so standard SDE theory does not apply; the assumptions replace global Lipschitz bounds by growth conditions in a conserved-mass-like norm $\|x\|_l$ and one-sided bounds that allow the dissipative nonlinearities typical of bimolecular chemistry. Moment bounds come from Dynkin's formula applied to $\|x\|_l^p$, and uniqueness and continuity come from a coupling in which both processes are driven by the same Poisson random measure, so that their difference only jumps when the thinned propensities disagree. Cubic autocatalysis violates the bounded-growth assumption, and its second moment indeed explodes in finite time.

## Sources

- Stefan Engblom, "On the Stability of Stochastic Jump Kinetics", Applied Mathematics 05 (2014), 3217–3239, <https://doi.org/10.4236/am.2014.519300>; numbering as in arXiv:1202.3892: Assumption 4.1, Propositions 3.5–3.6 and 4.2, Theorems 4.5 and 4.7–4.12, Corollary 4.11.
