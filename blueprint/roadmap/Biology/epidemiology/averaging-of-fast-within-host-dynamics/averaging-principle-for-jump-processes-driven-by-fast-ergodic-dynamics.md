# Averaging principle for index jump processes driven by fast ergodic dynamics

**Setting.** Let $E = \bigsqcup_{i\in I} E_i$ be a disjoint union of measurable spaces indexed by a measurable set $I$. A fast process $X^{\mathrm{o}}$ stays in $E_i$ when started there. The process $\mathbf{X}^n$ follows the accelerated dynamics $X^{\mathrm{o}}_{n\cdot}$ inside the current $E_i$; it leaves at a time $\zeta = \inf\{t : G(\int_0^t b(X^{\mathrm{o}}_{ns})\,ds) \ge U\}$ for an absolutely continuous cdf $G$, a measurable rate $b : E \to [0,\infty)$ and an independent uniform $U$, and then restarts at a point drawn from a kernel $\pi(x,\cdot)$ on $E$. The *index process* is $\mathbf{I}^n_t = i$ iff $\mathbf{X}^n_t \in E_i$. Assume:
- (ergodicity) for each $i$ there is a probability measure $\mu_i$ on $E_i$ with $\frac1t\int_0^t h(X^{\mathrm{o}}_s)\,ds \to \mu_i(h)$ almost surely for every admissible $h$ and every start in $E_i$;
- (uniform integrability) $\big(\frac1n\int_0^{nt}b(X^{\mathrm{o}}_s)\,ds\big)_{n\ge1}$ is uniformly integrable.

**Theorem.** Let $\mathbf{I}$ be the pure jump (semi-Markov) process on $I$ that, in state $i$, waits a time with cdf $t \mapsto G(t\,\mu_i(b))$ and then jumps to $j$ with law
$$K(i, dj) = \int_{E_i}\frac{\mu_i(dx)\,b(x)}{\mu_i(b)}\,\pi(x, E_{dj}).$$
1. For every $T > 0$ and bounded $f$, $\mathbf{E}^n_{x_i}\big[f(\mathbf{X}^n_{\tau_1^n})\mathbf{1}\{\tau_1^n \le T\}\big] \to G(T\mu_i(b))\int\frac{\mu_i(dx)}{\mu_i(b)}\,b(x)\,\pi(x,f)$; more generally the jump times and post-jump positions converge jointly in law, and the index chain $(\mathbf{I}^n_{\tau^n_k})_k$ with its holding times converges to that of $\mathbf{I}$.
2. The finite-dimensional laws of $\mathbf{I}^n$ before the $k$-th jump converge to those of $\mathbf{I}$, and $\liminf_n \mathbf{E}[f(\mathbf{I}^n_T)\mathbf{1}\{T < \tau^n_\infty\}] \ge \mathbf{E}[f(\mathbf{I}_T)\mathbf{1}\{T < \tau_\infty\}]$ for $f \ge 0$, with equality in the limit if $\mathbf{I}$ does not explode.
3. If $\mathbf{I}$ is non-explosive on $[0,T]$ and its marginals are tight, $\mathbf{I}^n \to \mathbf{I}$ in law in the Skorokhod space $D([0,T], I)$.

**Applications.**
- (Typed branching.) Individuals whose reproduction depends on a fast internal type converge to a continuous-time Galton–Watson process with averaged branching rate and averaged offspring law.
- (Epidemics with viral loads.) On a graph, each infected individual carries a viral load $Y$ that evolves fast and ergodically with stationary law $\nu$; a susceptible is infected by an infected neighbor with load $y$ at rate $\kappa_{0\to1}(y)$ and an infected individual with load $y$ heals at rate $\kappa_{1\to0}(y)$. If $Y$ converges to $\nu$ in total variation and the time averages of $\kappa_{0\to1}(Y), \kappa_{1\to0}(Y)$ are uniformly integrable, the susceptible/infected configuration converges in the Skorokhod topology to the classical contact process with infection rate $\nu(\kappa_{0\to1})$ and healing rate $\nu(\kappa_{1\to0})$.

## Expansion

Under acceleration the fast component explores its stationary law $\mu_i$ between slow jumps, so the cumulative hazard $\int_0^t b(X^{\mathrm{o}}_{ns})\,ds$ converges to $t\,\mu_i(b)$ by the ergodic theorem, giving the holding-time law $G(t\mu_i(b))$; conditional on a jump, the position from which it happens is distributed as $\mu_i$ tilted by $b$, giving the averaged jump kernel. Uniform integrability upgrades almost-sure ergodic averages to convergence of expectations, and no regularity of $b$ is needed because the convergence is in the strong (bounded measurable) sense. Iterating over successive jumps via the semi-Markov construction gives convergence of the whole jump sequence, and tightness plus non-explosion gives the Skorokhod statement.

## Sources

- V. Kagan, E. Strickler, D. Villemonais, "Averaging principle for jump processes depending on fast ergodic dynamics", arXiv:2510.21284 (2025), Section 2 (construction, Propositions 2.1–2.4), Assumptions and Proposition 3.1, Theorem 3.2, Corollaries 3.3–3.4, Proposition 3.5 and Theorem 3.6 (Section 3), Propositions 4.1–4.2 (Section 4), <https://doi.org/10.48550/arXiv.2510.21284>.
