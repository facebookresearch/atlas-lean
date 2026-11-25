# Bayes rationality

In a partition model with a prior $p$, a probability distribution on a finite set $\Omega$ of states, player $i$ has information
partition $\mathcal P_i$ and plays $s_i(\omega)$ at the state $\omega$. Player $i$ is Bayes rational at
$\omega$ when no action $k$ has a lower conditional expected cost given $i$'s information:

$$\mathbb E\bigl[c_i(s) \mid \mathcal P_i\bigr](\omega) \le \mathbb E\bigl[c_i(k, s_{-i}) \mid \mathcal P_i\bigr](\omega)\quad\text{for every action } k.$$

Aumann states the condition for payoffs $h_i = -c_i$, with the inequality reversed. On a null cell
the conditional expectations are $0$ (with the convention $x/0 = 0$) and the condition holds trivially.

## Related topics

- [Bayes rationality without normalisation](is-bayes-rational-iff-sum.md): on nonnull cells,
  the equivalent inequality between sums weighted by the prior.

## Sources

- R. J. Aumann, "Correlated equilibrium as an expression of Bayesian rationality", Econometrica 55(1) (1987), 1–18, §3, p. 7 (definition of Bayes rationality) and footnote 8 (conditional expectation given a partition).
