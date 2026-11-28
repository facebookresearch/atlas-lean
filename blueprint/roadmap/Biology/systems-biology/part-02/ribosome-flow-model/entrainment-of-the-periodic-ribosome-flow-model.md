# Entrainment of the periodic ribosome flow model

**Setting.** In the [ribosome flow model](ribosome-flow-model-and-its-globally-attracting-steady-state.md), let the initiation rate $\lambda_0(t)$ and transition rates $\lambda_1(t), \dots, \lambda_n(t)$ be continuous functions of time satisfying:

1. uniform bounds $0 < \delta_1 \le \lambda_i(t) \le \delta_2$ for all $i$ and $t \ge 0$;
2. all are periodic with a common minimal period $T > 0$ (some may be constant, but not all).

This is the **periodic ribosome flow model** (PRFM).

**Theorem.** The PRFM admits a unique $T$-periodic solution $\gamma : \mathbb{R}_{\ge 0} \to \operatorname{int} C^n$, and every trajectory converges to it:

$$\lim_{t\to\infty} |x(t, a) - \gamma(t)| = 0 \qquad \text{for all } a \in C^n = [0,1]^n .$$

In particular the translation rate $R(t) = \lambda_n(t) x_n(t)$ converges to the $T$-periodic function $\lambda_n(t)\gamma_n(t)$. The conclusion holds when only the initiation rate oscillates and the transition rates are constant, or when the initiation rate is constant and some transition rates oscillate.

## Depends on

- [Ribosome flow model and its globally attracting steady state](ribosome-flow-model-and-its-globally-attracting-steady-state.md)

## Proof depends on

- [Entrainment of contracting systems to periodic inputs](../contraction-and-entrainment/entrainment-of-contracting-systems-to-periodic-inputs.md)

## Expansion

The proof uses contraction. The RFM is on the verge of contraction: it is non-expanding in the $\ell_1$ norm on the whole cube, and after an arbitrarily short time every trajectory enters a compact subset of the interior on which the $\ell_1$ matrix measure of the Jacobian is strictly negative, so the time-varying system contracts there. A contracting $T$-periodic system has a unique periodic solution: the period map $a \mapsto x(T, a)$ maps the invariant cube into itself (Brouwer gives a fixed point, i.e. a periodic solution) and contraction makes all trajectories converge to it. Biologically, cell-cycle-dependent tRNA levels or initiation factors make translation of cell-cycle genes oscillate with the cell-cycle period; slow (rate-limiting) constant transition rates attenuate the oscillation amplitude as it propagates along the mRNA, but cannot prevent entrainment.

## Sources

- M. Margaliot, E. D. Sontag, T. Tuller, "Entrainment to periodic initiation and transition rates in a computational model for gene translation", PLoS ONE 9 (2014) e96039, Results (assumptions (4), Remark 1, Theorem 2, Examples 1–2) and Methods (contraction-based proof), <https://doi.org/10.1371/journal.pone.0096039>.
