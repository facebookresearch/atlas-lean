# Lebesgue angular length of a strict circular sublevel set

For `u:ℂ→EReal` and
arbitrary real `r,K`, let `S=(0,2π]∩{θ | u(circleMap 0 r θ)<−(K:EReal)}`. Its angular
length is `ℓ=volume(S)∈ℝ≥0∞`, using unnormalized Lebesgue measure on the real angle
variable, not division by `2π` or physical arc length. The circle is centered at zero and
has radius `|r|`. At `r=0`, `ℓ=ENNReal.ofReal(2π)` when `u(0)<−(K:EReal)`, and `ℓ=0`
otherwise.
