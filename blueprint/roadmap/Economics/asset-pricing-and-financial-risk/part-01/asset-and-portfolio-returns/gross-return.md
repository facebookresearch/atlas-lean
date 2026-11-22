# Gross return over one period

Simple gross return over one period: terminal price divided by initial price.
A zero terminal price is a valid total loss, `grossReturn 100 0 = 0`. Total: at
`P₀ = 0` this is the junk value `0` (by the convention `x / 0 = 0`), not a return.
