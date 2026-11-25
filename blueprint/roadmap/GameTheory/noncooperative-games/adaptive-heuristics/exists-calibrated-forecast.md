# Asymptotic calibration

For every $\varepsilon > 0$ there are a grid $\{0, 1/k, \dots, 1\}$ and a randomised forecasting
rule such that, against every Nature who chooses each outcome knowing the past but not the
current randomisation, the calibration score after $t$ rounds is below $\varepsilon$ with
probability greater than $1 - \varepsilon$ for all large $t$. Deterministic forecasters cannot
achieve this (Oakes 1985; Dawid 1985).

Foster and Vohra's forecast chooses, each round, a distribution on the grid satisfying the
conservation condition of their equation (2), which is the
[regret-invariance condition](../correlated-equilibria/is-regret-invariant.md) for the regrets of
replacing one forecast by another; they take $k \approx 1/\varepsilon^2$. Their definition of
$\varepsilon$-calibration asks that $\lim_t \Pr(C_t < \varepsilon) > 1 - \varepsilon$; the
statement here asks for the inequality for all large $t$, without the existence of the limit.
It is therefore weaker than their definition, which implies it.
Section 4 of their paper records a non-constructive proof by Sergiu Hart through the minimax
theorem.

## Background

- [Von Neumann's minimax theorem](../von-neumann-s-minimax-theorem/README.md): the tool of
  Hart's existence argument.

## Sources

- D. P. Foster and R. V. Vohra, "Asymptotic calibration", Biometrika 85(2) (1998), 379–390, §3 (Rules 1–3, Definition of $\varepsilon$-calibration), §4, Theorem 1 (§5).
