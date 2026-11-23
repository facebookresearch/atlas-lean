# Manning discharge of a rectangular channel

For a combined prefactor `C` collecting roughness and slope (`C = √S / n` in Manning's law), a
channel width `b` and a depth `h` (real numbers), the rectangular-channel Manning discharge is
`C * (b * h) * ((b * h) / (b + 2 * h)) ^ (2 / 3)` (real power), with flow area `b * h` and
hydraulic radius `(b * h) / (b + 2 * h)`. It is defined for all real inputs, with the conventions
`x / 0 = 0`, `0 ^ y = 0` for `y ≠ 0` and `x ^ y = |x| ^ y * cos (π y)` for `x < 0`: the value is
`0` when `b + 2 * h = 0`, and a negative hydraulic radius `r` enters as `-|r| ^ (2 / 3) / 2`. The
intended domain is `C > 0`, `b > 0` and `h > 0`.
