# Count Of Amount dim Scale

Rescaling an amount and `N_A` together leaves the count unchanged: the amount
coordinate rescales by `dimScale amountDim` and the inverse-amount coordinate of `N_A`
by its inverse. This is the counter-case to holding `N_A` fixed while rescaling the
amount.
