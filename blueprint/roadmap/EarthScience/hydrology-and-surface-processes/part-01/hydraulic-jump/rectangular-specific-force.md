# Specific force in a rectangular channel

For a rectangular open channel at depth `h`, with discharge per unit width `q` and gravity `g`
(real numbers), the specific force (momentum function) per unit width is
`M(h) = h ^ 2 / 2 + q ^ 2 / (g * h)`: the hydrostatic pressure-force term plus the momentum-flux
term, each divided by the specific weight and the channel width. It is physically meaningful for
`g > 0` and `h > 0`. It is defined for all real inputs, with the convention `x / 0 = 0`: when
`g = 0` or `h = 0` the momentum-flux term is `0` and `M(h) = h ^ 2 / 2`.
