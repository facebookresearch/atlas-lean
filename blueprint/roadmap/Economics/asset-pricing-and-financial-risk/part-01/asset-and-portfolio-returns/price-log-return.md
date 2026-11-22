# Log return between two prices

Log return over one price period: the log return of the gross return,
`logReturn (grossReturn P₀ P₁)`. The definition is total: at nonpositive prices
it returns a junk value, e.g. `priceLogReturn 100 0 = Real.log 0 = 0`, equal to
the unchanged-price value `priceLogReturn 100 100`, although the gross return
`grossReturn 100 0 = 0` of that total loss is valid. A genuine log return
requires `0 < P₀` and `0 < P₁`, as assumed by `priceLogReturn_add`.
