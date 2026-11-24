# For countable $S$, sets determined by $Y_0, \dots, Y_n$ are measurable

Let $S$ be a countable measurable space in which every singleton is measurable (so every subset of
$S$ is measurable), and give step sequences $\omega = (\omega_i)_{i \in \mathbb{N}}$,
$\omega_i = (\xi_i, E_i) \in S^S \times \mathbb{R}$, the product σ-algebra built from the product
σ-algebra on maps $S \to S$ and the Borel σ-algebra on $\mathbb{R}$. Let $x \in S$ and
$n \in \mathbb{N}$, and let $A$ be a set of step sequences whose membership depends only on the
first $n + 1$ states $Y_0, \dots, Y_n$ of the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$: if $\omega \in A$ and $Y_j(x, \omega') = Y_j(x, \omega)$ for every $j \le n$, then
$\omega' \in A$. Then $A$ is measurable; no measurability of $A$ is assumed.
