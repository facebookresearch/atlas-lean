# Film and layer drops of one heat rate Q give Q = ΔT/R = A U ΔT

Let `A`, `h_in` and `h_out` be positive, and `L i > 0` and `k i > 0` for every `i < n`. Let `Temp 0`
be the inside air temperature, `Temp 1, …, Temp (n+1)` the successive interface temperatures after
the inside film and each layer, and `Temp (n+2)` the outside air temperature. Suppose one heat rate
`Q` produces all the drops: `Temp 0 - Temp 1 = Q/(h_in A)`,
`Temp (i+1) - Temp (i+2) = Q L i/(k i A)` for every `i < n`, and
`Temp (n+1) - Temp (n+2) = Q/(h_out A)`. Then

`Q = (Temp 0 - Temp (n+2)) / R`,

with the [series resistance](thermal-series-resistance.md)
`R = 1/(h_in A) + ∑_{i < n} L i/(k i A) + 1/(h_out A)`.

Equivalently, `Q = A U (Temp 0 - Temp (n+2))` with the
[overall coefficient](thermal-overall-coefficient.md) `U = 1/(A R)`.
