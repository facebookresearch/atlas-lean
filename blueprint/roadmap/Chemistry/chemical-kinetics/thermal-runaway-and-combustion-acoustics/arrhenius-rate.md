# Net Arrhenius heating rate with Newton cooling

Zeroth-order Arrhenius heat-release rate with Newton cooling:
`rate(T) = G * exp(-B / T) - H * (T - Tₐ)`, for heat-generation scale `G`, cooling coefficient `H`,
activation temperature `B = E / R`, and ambient temperature `Tₐ`. Read for `T > 0`. It is defined
for every real `T`: for `T = 0` the convention `x / 0 = 0` makes it `G + H * Tₐ`.
