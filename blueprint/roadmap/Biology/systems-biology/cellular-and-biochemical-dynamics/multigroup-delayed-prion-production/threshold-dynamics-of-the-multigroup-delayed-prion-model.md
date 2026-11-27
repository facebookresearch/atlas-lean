# Threshold dynamics of the multigroup delayed prion model

**Setting.** Take the $n$-neuron delay system for normal prion protein $x_i$ and misfolded prion protein $y_i$ with its disease-free equilibrium $E_0 = (K_1/\mu_1, \dots, K_n/\mu_n, 0, \dots, 0)$ and basic reproduction number $\mathcal{R}_0 = \rho(F)$, as in [the basic reproduction number of the multigroup delayed prion model](basic-reproduction-number-of-the-multigroup-delayed-prion-model.md). Initial data are $(x_{i0}, \varphi_i) \in \mathbb{R}_+ \times C([-T,0], \mathbb{R}_+)$.

**Theorem.**
1. *Extinction.* If $\mathcal{R}_0 < 1$, then $E_0$ is globally asymptotically stable.
2. *Instability.* If $\mathcal{R}_0 > 1$, then $E_0$ is locally unstable.
3. *Uniform persistence.* If $\mathcal{R}_0 > 1$, there is $\varepsilon > 0$ such that for every initial condition with $\varphi_i(0) \ne 0$ for $i = 1, \dots, n$,

$$\liminf_{t\to\infty} y_i(t) > \varepsilon, \qquad i = 1, \dots, n.$$

4. *Endemic equilibrium.* If the minimum row sum of $F$ is strictly larger than $1$, the system has at least one endemic equilibrium.

Moreover, if a single neuron has $R_{0\tilde\imath} > 1$, then $\mathcal{R}_0 > 1$ and $\limsup_{t\to\infty} y_{\tilde\imath}(t) > \varepsilon_{\tilde\imath}$ for some $\varepsilon_{\tilde\imath} > 0$.

## Depends on

- [Basic reproduction number of the multigroup delayed prion model](basic-reproduction-number-of-the-multigroup-delayed-prion-model.md)
- [Hurwitz stability of the infected subsystem is equivalent to R0 < 1](../../../epidemiology/next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Proof sketch

Local stability uses the van den Driessche–Watmough lemma: for $M \ge 0$ and a nonsingular M-matrix $V$, $\rho(MV^{-1}) < 1$ if and only if all eigenvalues of $M - V$ have negative real part. Global extinction follows by comparison: since $\beta \le 1$, $\limsup x_i \le K_i/\mu_i$, so $y$ is eventually dominated by the linear cooperative system $\dot y = (M - V + \epsilon)y$, which decays when $\rho(F) < 1$. Persistence is proved with weak persistence ($\limsup y_i > \varepsilon$, then $\liminf x_i > \tilde\varepsilon$) upgraded to uniform persistence by the dynamical-systems persistence theory for semiflows on $\mathbb{R}_+^n \times C^+$. The paper conjectures that $\mathcal{R}_0 > 1$ alone already gives an endemic equilibrium.

## Sources

- Mostafa Adimy, Abdennasser Chekroun, Laurent Pujo-Menjouet and Mattia Sensi, "A multigroup approach to delayed prion production", *Discrete and Continuous Dynamical Systems - B* 29 (2024), 2972–2998, <https://doi.org/10.3934/dcdsb.2023209>. Preprint version: arXiv:2307.05524 (2023), Theorem 1, Lemma 1, Corollary 1 (Section 4), Theorem 2 and Conjecture 1 (Section 5), Propositions 3–5 and Theorem 3 (Section 6), <https://doi.org/10.48550/arXiv.2307.05524>.
