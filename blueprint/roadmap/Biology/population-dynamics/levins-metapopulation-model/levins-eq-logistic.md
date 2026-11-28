# For c > 0 and e < c, the explicit solution is a logistic curve

**Logistic form.** For real numbers `c > 0` and `e < c` and all real `p₀` and `t`, the
[explicit solution](levins.md) with `p(0) = p₀` equals the
[logistic curve](../logistic-growth-equation/logistic.md) with rate `c - e` and carrying capacity
`p* = 1 - e / c`: `p(t) = p* p₀ e^{(c - e) t} / (p* + p₀ (e^{(c - e) t} - 1))`. The two denominators
vanish at the same times, where both sides are `0` by the convention `x / 0 = 0`. Here `p* > 0`, and
`p* ≤ 1` exactly when `e ≥ 0`.
