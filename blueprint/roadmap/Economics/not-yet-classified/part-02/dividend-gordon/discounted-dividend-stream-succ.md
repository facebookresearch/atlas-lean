# Discounted Dividend Stream succ

Shifting the discounted dividend stream by one date gives exactly the
growing-perpetuity stream: at date `t + 1` the dividend is `D₁ * (1 + g) ^ t`,
discounted by `discountFactor r (t + 1)`.
