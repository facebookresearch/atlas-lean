# Quantifier elimination preserves truth

Let $\mathrm{qe}$ be the quantifier elimination map
on formulas. For every formula $\varphi$ and every environment $e : \mathbb{N} \to \mathbb{R}$,
the formula $\mathrm{qe}(\varphi)$ holds in $\mathbb{R}$ under $e$ if and only if $\varphi$ holds
in $\mathbb{R}$ under $e$.

Together with the statement that $\mathrm{qe}(\varphi)$ is always quantifier free, this is
Tarski's quantifier elimination theorem, stated for $\mathbb{R}$.

## Sources

- Tarski, 'A Decision Method for Elementary Algebra and Geometry' (1951); Collins, 'Quantifier elimination for real closed fields by cylindrical algebraic decomposition' (1975); Mahboubi, 'Programming and certifying a CAD algorithm in the Coq system' (2006); Cohen and Mahboubi, 'Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination' (2012). Problem `rcf_quantifier_elimination` of the lean-eval benchmark.
