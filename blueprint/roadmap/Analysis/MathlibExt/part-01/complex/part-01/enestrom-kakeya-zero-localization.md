---
article_id: af_542941667918f9b94df45398
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.EnestromKakeya.enestrom_kakeya_zero_localization
---

# Enestrom Kakeya

Classical Eneström–Kakeya theorem: if `f(z) = a₀ + a₁ z + ⋯ + aₙ zⁿ` has
positive (real) coefficients, then every complex zero `z` of `f` satisfies
`ρ₁ ≤ ‖z‖ ≤ ρ₂`, where `ρ₁` is the minimum and `ρ₂` the maximum of the adjacent
ratios `aₖ / aₖ₊₁` for `0 ≤ k ≤ n - 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.EnestromKakeya](../../../../../../sources/v2/MathlibExt.md)
- Karl Dilcher and Larry Ericksen, "Polynomials Whose Coefficients Are Stern Numbers," Journal of Integer Sequences 24 (2021), Article 21.10.3, Theorem 4.1 (quoted there as the classical Eneström–Kakeya theorem). Public TeX URL: `https://cs.uwaterloo.ca/journals/JIS/VOL24/Dilcher/dilcher51.tex` Retrieved TeX SHA-256: `72f3e8444cd0fd6b5f55e89d6427f130b294841131d89c994fe3bb2971dbb19e` Proves `Wanted` entry `enestrom_kakeya_zero_localization`.
