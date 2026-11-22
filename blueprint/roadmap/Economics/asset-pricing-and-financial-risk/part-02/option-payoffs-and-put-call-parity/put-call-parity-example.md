# Numerical example of put–call parity

Concrete instance: one terminal state `ω = 110`, `S0 = 110`, `D = 0`,
`K = 100`, `R = 1` (zero interest), and the one-state pricing functional
`price f = f 110 / 1`. Then `C - P = 10 = 110 - 100`. (For another gross return
`R > 0`, the one-state functional `price f = f ω / R` satisfies `hStock` exactly
when `ω = R * (S0 - D)`; the `R = 1` case keeps the arithmetic exact.)
