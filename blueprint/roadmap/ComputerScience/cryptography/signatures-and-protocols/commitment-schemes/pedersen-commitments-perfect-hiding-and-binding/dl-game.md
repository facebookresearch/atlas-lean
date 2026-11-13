# Dl Game

The discrete-logarithm experiment (Katz and Lindell, Section 8.3.2, with `h` from
`paramGen`): `h ← paramGen q g`, `r ← A.coins`, and the adversary wins if its output `x'`
satisfies `g ^ x' = h`. Unlike Katz and Lindell, `h = 1` is excluded, matching the binding
experiment. Wave 3: unify with the Wave 1 Assumptions DLP game.
