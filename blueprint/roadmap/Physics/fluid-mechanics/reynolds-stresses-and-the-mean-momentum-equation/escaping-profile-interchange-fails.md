# Without domination, derivative and ensemble mean need not commute

For the [escaping profile](escaping-profile.md) `φ(s, ω) = (s³ / ω²) exp(-s² / ω)`:

- Lebesgue measure restricted to `(0, 1]` is a probability measure;
- for all real `ω` and `s`, `s ↦ φ(s, ω)` has the derivative
  `φ′(s, ω) = (3 s² / ω² - 2 s⁴ / ω³) exp(-s² / ω)` at `s`, which is `0` at `s = 0`;
- for every real `s`, `∫_{(0, 1]} φ(s, ω) dω = s exp(-s²)`;
- this mean has the derivative `1` at `s = 0`, not the mean `0` of the derivatives;
- there is no `ε > 0` and no function `B` integrable on `(0, 1]` with `|φ′(s, ω)| ≤ B(ω)` for
  almost every `ω` and every `s` with `|s| < ε`.

So the domination hypothesis of the [mean momentum equation](mean-momentum.md) cannot be dropped.
