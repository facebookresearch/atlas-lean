# Selection principle for N-branching Brownian motion

**Model.** The $N$-BBM with selection consists of $N$ particles on $\mathbb R$ that move as independent standard Brownian motions and branch at rate $1$; at each branching event the leftmost particle is removed, so the population size stays $N$. It models a population of fixed size under truncation selection on a trait (fitness) that diffuses. Let $\vec Y^N_t$ denote the particle positions seen from the leftmost particle, and $\Theta^N(x_1,\dots,x_N) = \frac1N\sum_i\delta_{x_i}$. As $N \to \infty$ on finite time intervals, the empirical measure follows the free-boundary problem

$$\partial_t u = \tfrac12\Delta u + u \ \ (x > L_t), \qquad u(t, L_t) = 0, \qquad \int_{L_t}^\infty u(t,y)\,dy = 1,$$

whose travelling waves have speeds $c \ge \sqrt 2$; the minimal one is $\pi_{\min}(x) = 2x e^{-\sqrt 2 x}$, $x > 0$, with speed $c_{\min} = \sqrt 2$.

**Theorem.**
1. For each fixed $N$, $\vec Y^N$ satisfies Doeblin's condition, so it has a unique stationary law $\psi^N$ and converges to it in total variation at a geometric rate; the leftmost particle has an almost-sure asymptotic speed $v_N \in (0, \sqrt 2)$.
2. *(Selection principle.)* If $\vec Y^N \sim \psi^N$, then $\Theta^N(\vec Y^N) \to \pi_{\min}$ weakly in probability as $N \to \infty$; indeed $\mathbb E_{\psi^N}\big[W_1\big(\Theta^N(\vec Y^N), \pi_{\min}\big)\big] \to 0$.

## Expansion

The free-boundary PDE has a continuum of travelling waves, like the Fisher–KPP equation, so the hydrodynamic limit alone does not say which profile the stationary $N$-particle system approaches. The finite system cannot sustain the heavy, slowly decaying tails of the faster waves: its speed is at most $\sqrt 2$, and any subsequential limit of the stationary empirical measures is a stationary law for the PDE flow advancing at speed at most $\sqrt 2$. Since $\pi_{\min}$ is the only travelling wave compatible with that bound, the limit is $\pi_{\min}$. This is the particle analogue of the Brunet–Derrida picture for pulled fronts, and parallels the selection principle for Fleming–Viot particle systems approximating quasi-stationary distributions.

## Sources

- J. Berestycki, O. Tough, "Selection principle for the N-BBM", arXiv:2407.05792 (2024), Theorems 1.1, 1.2, 1.4 and Proposition 2.2, <https://doi.org/10.48550/arXiv.2407.05792>.
