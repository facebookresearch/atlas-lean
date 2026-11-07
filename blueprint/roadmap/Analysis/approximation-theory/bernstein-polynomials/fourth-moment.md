# Fourth central moment of the Bernstein weights

For `n ≠ 0`,
`∑ k : Fin (n + 1), (x - k / n) ^ 4 * bernstein n k x = x (1 - x) (1 + 3 (n - 2) x (1 - x)) / n³`,
i.e. `E[(S - n x) ^ 4] = n x (1 - x) (1 + 3 (n - 2) x (1 - x))` for `S ~ Bin(n, x)`.
