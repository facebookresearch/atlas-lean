# Bayes rationality without normalisation

In a partition model with a prior $p$, a probability distribution on a finite set $\Omega$ of states,
where player $i$ has information partition $\mathcal P_i$ and the action profile at the state $x$ is
$s(x)$, player $i$ is Bayes rational at $\omega$ if and only if, for every action $k$,

$$\sum_{x \in P_i(\omega)} p(x)\,\bigl(c_i(s(x)) - c_i(k, s_{-i}(x))\bigr) \le 0.$$

On a cell of positive probability this is the conditional inequality multiplied by the probability
of the cell; on a null cell both conditions hold trivially.

## Background

- [Bayes rationality](is-bayes-rational.md): the condition rewritten.
- [Conditional expectation given a partition](cond-exp-cell.md): the normalised form.

## Sources

- R. J. Aumann, "Correlated equilibrium as an expression of Bayesian rationality", Econometrica 55(1) (1987), 1–18, p. 7–8 (the cell-wise inequality $E(h^i(s) \mid P) \ge E(h^i(s^{-i}, s^i) \mid P)$ in the proof of the Main Theorem).
