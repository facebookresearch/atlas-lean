# Klein's inequality for the matrix relative entropy

The matrix relative entropy is
nonnegative (J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
arXiv:1501.01571v1, Proposition 8.1.3; Tropp, *From joint convexity of quantum relative entropy
to a concavity theorem of Lieb*, arXiv:1101.1070v1, Fact 3). For positive-definite matrices `X`
and `Y` over `ℝ` or `ℂ`,
`re tr (X log Y) - re tr (X log X) ≤ re tr Y - re tr X`, where `log` is the matrix function
`cfc Real.log`; that is, `tr (X log X - X log Y - X + Y) ≥ 0`.
