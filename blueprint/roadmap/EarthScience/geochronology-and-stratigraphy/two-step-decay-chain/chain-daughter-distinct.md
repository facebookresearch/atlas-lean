# Chain Daughter Distinct

Daughter inventory for distinct rates `l1 ≠ l2`:
`D0 * exp (-l2 * t) + P0 * l1 / (l2 - l1) * (exp (-l1 * t) - exp (-l2 * t))`.
At `l1 = l2` Lean's division by zero drops the feeding term, and the result solves the daughter
ODE only when `l1 * P0 = 0`; use `chainDaughterRepeated` for equal rates.
