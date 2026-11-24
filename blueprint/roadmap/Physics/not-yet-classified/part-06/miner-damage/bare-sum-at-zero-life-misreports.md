# Bare Sum at zero life misreports

Zero life rejected, control. Without the positivity precondition, Lean's `x / 0 = 0` makes
the bare sum `∑ i, n i / N i` blind to the count at a class `j` with `N j = 0`: any count there
registers no damage, although a vanishing life would mean immediate failure. This is why
`minerDamage` demands `∀ i, 0 < N i`.
