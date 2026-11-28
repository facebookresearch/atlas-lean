# Fixation and ergodicity of Λ-Wright–Fisher processes with coordinated selection and mutation

**Model.** In an infinite two-type population, the frequency $X_t$ of type $a$ solves

$$\begin{aligned}
dX_t ={}& \sqrt{\Lambda(\{0\})X_t(1-X_t)}\,dW_t + \int z\big(\mathbf{1}_{\{u \le X_{t-}\}}(1 - X_{t-}) - \mathbf{1}_{\{u > X_{t-}\}}X_{t-}\big)\tilde N(dt,dz,du)\\
&+ \big(d_{\mathbf{s}}(X_t) + \theta_a(1 - X_t) - \theta_A X_t\big)dt + \int |z|\big(\mathbf{1}_{\{z \ge 0\}}(1 - X_{t-}) - \mathbf{1}_{\{z<0\}}X_{t-}\big)M(dt,dz)\\
&+ \int z\,X_{t-}(1 - X_{t-})\,S(dt,dz),
\end{aligned}$$

with: neutral $\Lambda$-reproduction ($W$ a Brownian motion, $\tilde N$ compensated Poisson with intensity $dt\,z^{-2}\Lambda(dz)\,du$, $\Lambda$ a finite measure on $[0,1]$); frequency-dependent selection $d_{\mathbf{s}}(x) = \sum_{\ell=2}^{\kappa}\beta_\ell\sum_{i=0}^{\ell}\binom{\ell}{i}x^i(1-x)^{\ell-i}\big(p_i^{(\ell)} - \frac{i}{\ell}\big)$, $\beta_\ell \ge 0$, $p_i^{(\ell)} \in [0,1]$, $p_0^{(\ell)} = 0$, $p_\ell^{(\ell)} = 1$ (any drift $x(1-x)\sigma(x)$ with polynomial $\sigma$ has this form); coordinated selection by an environment $S$ with intensity $dt\,|z|^{-1}\mu(dz)$ on $(-1,1)$, which may favour either type (bidirectional selection); individual mutation rates $\theta_a, \theta_A \ge 0$; and coordinated mutation $M$ with intensity $dt\,|z|^{-1}\nu(dz)$.

**Bernstein duality.** Write $H(x, v) = \sum_{i=0}^{n} v_i\binom{n}{i}x^i(1-x)^{n-i}$ for $v \in \mathbb{R}^{n+1}$. The Bernstein coefficient process $V$ is the continuous-time Markov chain on coefficient vectors (of varying length $L_t + 1$, $L_t = \dim V_t - 1$) that jumps from $w \in \mathbb{R}^{n+1}$ to:

- $C^{n,k}w \in \mathbb{R}^{n-k+2}$, $k \in \{2,\dots,n\}$ (coalescence of $k$ of the $n$ lines), at rate $\binom{n}{k}\lambda_{n,k}$, where $\lambda_{n,k} = \int_{[0,1]} z^{k-2}(1-z)^{n-k}\,\Lambda(dz)$ with $0^0 = 1$, so that $\lambda_{n,2} = \Lambda(\{0\}) + \int_{(0,1]}(1-z)^{n-2}\,\Lambda(dz)$;
- $D^{n,l}w \in \mathbb{R}^{n+l}$, $l \in \{2,\dots,\kappa\}$ (selective branching), at rate $n\beta_l$;
- $M_c^{n,\ell}w \in \mathbb{R}^{n-\ell+1}$, $\ell \in \{1,\dots,n\}$ and $c \in \{a, A\}$ (mutation to type $c$), at rate $\binom{n}{\ell}m^c_{n,\ell} + \mathbf{1}_{\{\ell=1\}}\,n\theta_c$, where

    $$m^a_{n,\ell} = \int_{(0,1)} z^{\ell-1}(1-z)^{n-\ell}\,\nu(dz), \qquad m^A_{n,\ell} = \int_{(-1,0)} |z|^{\ell-1}(1-|z|)^{n-\ell}\,\nu(dz);$$

- $S_c^{n,\ell}w \in \mathbb{R}^{n+\ell+1}$, $\ell \in \{1,\dots,n\}$ and $c \in \{a, A\}$ (coordinated selection favouring type $c$), at rate $\binom{n}{\ell}\sigma^c_{n,\ell}$, where

    $$\sigma^a_{n,\ell} = \int_{(0,1)} z^{\ell-1}(1-z)^{n-\ell}\,\mu(dz), \qquad \sigma^A_{n,\ell} = \int_{(-1,0)} |z|^{\ell-1}(1-|z|)^{n-\ell}\,\mu(dz).$$

The operators $C^{n,k}$, $D^{n,l}$, $M_c^{n,\ell}$ and $S_c^{n,\ell}$ are fixed finite-dimensional linear maps (given explicitly in Definition 3.2 of the source), and $V$ lives on the countable set of vectors obtained from $V_0$ by finitely many such maps. Then for all $x \in [0,1]$, $v$ and $t \ge 0$,

$$\mathbb{E}_x\big[H(X_t, v)\big] = \mathbb{E}_v\big[H(x, V_t)\big].$$

**Theorem.** Assume

$$\sum_{\ell=2}^{\kappa}\beta_\ell(\ell - 1) + \mu(-1,1) < \int_{[0,1]}|\log(1 - z)|\,\frac{\Lambda(dz)}{z^2} + \nu(-1,1) + \theta_a + \theta_A.$$

1. *No mutation* ($\theta = 0$, $\nu = 0$): for $X_0 = x \in (0,1)$, $X_t$ converges almost surely to $X_\infty \in \{0,1\}$ and

    $$\mathbb{P}_x(X_\infty = 1) = \mathbb{E}\big[H(x, V_\infty^{0,1})\big] \in (0,1),$$

    where $V_\infty^{0,1}$ has the unique invariant law of $V$ on coefficient vectors with first entry $0$ and last entry $1$.

2. *Bidirectional mutation* ($\theta_a + \nu(0,1) > 0$ and $\theta_A + \nu(-1,0) > 0$): $V$ is absorbed in finite time at a scalar $U_\infty$; $X$ never fixes, has a unique stationary distribution $\mathcal{L}$, the law of $X_t$ converges weakly to $\mathcal{L}$ from any start, and

    $$\int_{[0,1]} x^n\,\mathcal{L}(dx) = \mathbb{E}_{e_n}[U_\infty], \qquad n \ge 0,$$

    with $e_n$ the $(n+1)$-th unit vector of $\mathbb{R}^{n+1}$; these moments satisfy explicit linear recursions.

## Expansion

Moment duality struggles when selection can favour either type, because the dual must track signed contributions. Bernstein duality instead propagates the full coefficient vector of a Bernstein polynomial: reproduction events coalesce lineages (lowering the degree and averaging coefficients), selective events branch them (raising the degree by $\ell - 1$), and mutation or environment events act by fixed linear maps. The displayed condition is a drift criterion: the logarithmic rate at which $\Lambda$-coalescence and mutation shrink the vector length beats the rate at which selection and coordinated selection grow it, so the length process $L$ is positive recurrent. Without mutation the boundary coefficients are frozen and the interior ones converge in law, giving the fixation probability; with mutation in both directions the vector collapses to length one, and its terminal value gives the stationary moments.

## Sources

- Fernando Cordero, Sebastian Hummel and Grégoire Véchambre, "Bernstein duality revisited: Frequency-dependent selection, coordinated mutation and opposing environments", *Bernoulli* 32 (2026), 874–900, <https://doi.org/10.3150/25-bej1883>. Numbering as in the preprint arXiv:2407.01242v2, <https://arxiv.org/abs/2407.01242v2>: model (Section 2), Definition 2.1 (dual transitions and rates, Eqs. (2.7)–(2.9)), Definition 3.2 (operators), Theorem 2.2, Proposition 2.3, Theorem 2.4, Proposition 2.5, Theorem 2.6 and Proposition 2.7.
