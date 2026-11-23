# Rectangular Specific Force

Specific force (momentum function) per unit width for a rectangular
open channel: at depth `h`, with discharge per unit width `q` and gravity
`g`, it is `h ^ 2 / 2 + q ^ 2 / (g * h)`, the sum of the hydrostatic
pressure-force term and the momentum-flux term, each divided by the
specific weight and the channel width. It is physically meaningful for
`0 < g` and `0 < h`; outside that range the formula uses Lean's totalized
division and carries no physical meaning.
