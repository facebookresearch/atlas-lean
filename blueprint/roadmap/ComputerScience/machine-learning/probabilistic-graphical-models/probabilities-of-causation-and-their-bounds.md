# Probabilities of causation and their bounds

This node collects the probabilities of causation for binary treatment $X$ and outcome $Y$ in a finite
structural causal model and their bounds.

## Expansion

A sound expansion has separate pages for:

1. **Definitions.** $\mathrm{PNS} = P(y_x, y'_{x'})$; $\mathrm{PN} = P(y'_{x'} \mid x, y)$, defined when
   $P(x, y) > 0$; $\mathrm{PS} = P(y_x \mid x', y')$, defined when $P(x', y') > 0$.
2. **Bounds from experimental data.** $\max(0, P(y_x) - P(y_{x'})) \le \mathrm{PNS} \le \min(P(y_x), P(y'_{x'}))$.
3. **Identification under monotonicity** ($y_{x'}$ implies $y_x$ for every unit): $\mathrm{PNS} = P(y_x) - P(y_{x'})$,
   $\mathrm{PN} = (P(y) - P(y_{x'}))/P(x, y)$ when $P(x, y) > 0$, and $\mathrm{PS} = (P(y_x) - P(y))/P(x', y')$ when
   $P(x', y') > 0$.
4. **Bounds from combined data without monotonicity:**
   $\max\{0, (P(y) - P(y_{x'}))/P(x, y)\} \le \mathrm{PN} \le \min\{1, (P(y'_{x'}) - P(x', y'))/P(x, y)\}$ and
   $\max\{0, (P(y_x) - P(y))/P(x', y')\} \le \mathrm{PS} \le \min\{1, (P(y_x) - P(x, y))/P(x', y')\}$, under the same
   positivity conditions.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Finite recursive structural causal models.

## Related topics

- [The probability of necessity under monotonicity](structural-causal-models-and-counterfactuals/cf-prob-necessity.md)

## Sources

- J. Tian and J. Pearl, *Probabilities of causation: bounds and identification*, Annals of Mathematics and Artificial Intelligence 28 (2000) 287–313 (technical report R-271-A): Definition 9, the bounds of Section 4.2 (Eqs. (24)–(26) for combined data) and Theorem 3 (identification under monotonicity, Eqs. (40)–(42)). <https://ftp.cs.ucla.edu/pub/stat_ser/R271-A.pdf>
