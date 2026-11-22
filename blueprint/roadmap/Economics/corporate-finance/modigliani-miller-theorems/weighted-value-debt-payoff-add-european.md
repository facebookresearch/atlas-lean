# Weighted values of debt and equity sum to the firm value

Weighted-sum additivity for the split of a firm into debt (face `F`) and equity: for any
weights `ψ`, the weighted values of the debt and equity payoffs add up to the weighted value of
the firm payoff `V`. This is linearity of `weightedValue` applied to
`debtPayoff_add_europeanCallPayoff`, not Modigliani–Miller I: valuing every payoff with the same
linear functional builds the additivity in. The price statement is
`modiglianiMiller_of_no_arbitrage`.
