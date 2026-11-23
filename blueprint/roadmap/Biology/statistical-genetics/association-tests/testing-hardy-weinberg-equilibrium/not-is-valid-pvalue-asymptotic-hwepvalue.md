# The asymptotic HWE test is anti-conservative for sparse counts

Under HWE with `N = 10`
individuals and `n_A = 2` copies of `A`, the chi-square p-value is not a valid p-value: the
level-`0.05` asymptotic test rejects with null probability at least `1/19 > 0.05`. The exact
p-value is valid in the same model (`isValidPValue_hweExactPValue`).

## Sources

- Emigh (1980); Wigginton, Cutler and Abecasis (2005).
