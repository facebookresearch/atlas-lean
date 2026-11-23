# Sum nonneg of target binary

Core termwise estimate behind target-only `f3` positivity: a finite sum of
`(wC e - wA e) * (wC e - wB e) * len e` is nonnegative when every `len e` is
nonnegative, every target weight `wC e` is `0` or `1`, and the source weights
`wA e`, `wB e` lie in `[0, 1]` (they need not be binary).
