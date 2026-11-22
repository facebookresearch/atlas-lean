# Finite-horizon government budget identity, present-value form

Iterating
the debt recursion, initial debt plus the present value of primary deficits through horizon
`n` equals the discounted terminal debt; the terminal debt is retained explicitly and not
assumed away:
`B 0 + presentValue (discountFactor r) (Finset.Icc 1 n) D = discountFactor r n * B n`.
Rewritten as `B t = (-D (t + 1) + B (t + 1)) / (1 + r)`, the debt recursion is the price
recursion of `FiniteDividendDiscount.finiteDividendDiscount` with cash flow `-D`.
