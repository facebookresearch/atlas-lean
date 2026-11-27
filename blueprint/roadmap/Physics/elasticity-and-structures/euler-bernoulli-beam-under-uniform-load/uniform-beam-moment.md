# Bending moment of the uniformly loaded beam

For real `w`, `EI`, `L` and `x`, the bending moment of the simply supported beam under uniform load
is `M(x) = -EI * y''(x)`, where `y(x) = w * (L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4) / (24 * EI)` is the
[deflection](uniform-load-deflection.md), positive downward, and `y''` is its second derivative: the
sagging-positive convention. It is defined for all real inputs; with the convention `x / 0 = 0` it
is identically `0` when `EI = 0`.
