# Dividend Stream

Dividend stream with first dividend `D₁` at date 1, growing at rate `g` per period.
`dividendStream D₁ g t` is the dividend paid at date `t`: `0` today (`t = 0`, no
dividend is paid at date 0) and `D₁ * (1 + g) ^ (t - 1)` for `t ≥ 1` (source clause:
"dividend `D_t = D₁ (1+g)^{t-1}` at dates `t ≥ 1`"). This is a genuinely date-indexed
dividend abstraction, distinct from the growing-perpetuity stream, which is indexed
from `0` at date 1.
