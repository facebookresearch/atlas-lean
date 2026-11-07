# Quantifier elimination over the reals

Quantifier elimination is a map sending each formula
$\varphi$ of the language of ordered rings to a formula $\operatorname{qe}(\varphi)$, subject to
two requirements: $\operatorname{qe}(\varphi)$ is quantifier free, and for every environment
$e : \mathbb{N} \to \mathbb{R}$ assigning a real number to each variable,
$\operatorname{qe}(\varphi)$ holds in $\mathbb{R}$ under $e$ if and only if $\varphi$ does.

The formula $\operatorname{qe}(\varphi)$ may mention additional variables, but only vacuously.

## Sources

- Tarski, 'A Decision Method for Elementary Algebra and Geometry' (1951); Collins, 'Quantifier elimination for real closed fields by cylindrical algebraic decomposition' (1975); Mahboubi, 'Programming and certifying a CAD algorithm in the Coq system' (2006); Cohen and Mahboubi, 'Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination' (2012). Via leanprover/lean-eval@38361be, problem `rcf_quantifier_elimination`.
