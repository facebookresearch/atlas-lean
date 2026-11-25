# Weighted values of debt and equity sum to the firm value

On a finite set of states `Ω`, for any real weights `ψ`, firm payoff `V` and face value `F`, the
weighted-sum values of the debt payoff `min(V(ω), F)` and of the equity payoff
`max(V(ω) - F, 0)` add up to the weighted-sum value of the firm payoff:
`∑_ω ψ(ω) * min(V(ω), F) + ∑_ω ψ(ω) * max(V(ω) - F, 0) = ∑_ω ψ(ω) * V(ω)`. This is linearity of
the weighted sum applied to the payoff identity `min(V, F) + max(V - F, 0) = V`, not
Modigliani–Miller I: valuing every payoff with the same linear functional builds the additivity
in. The price statement is Modigliani–Miller I, which assumes no funded arbitrage.
