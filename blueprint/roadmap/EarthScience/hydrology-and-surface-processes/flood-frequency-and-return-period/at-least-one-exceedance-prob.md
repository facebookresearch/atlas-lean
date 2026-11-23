# At least one exceedance prob

At least one exceedance in `n` years: if `p` is the annual
exceedance probability in `[0, 1]`, the yearly no-exceedance
events `F i` are independent, and each has probability `1 - p`,
then the probability of an exceedance in at least one of the
`n` years is `1 - (1 - p) ^ n`. Independence and the constant
annual probability are assumptions of the model, supplied here
through `no_exceedance_prob`.
