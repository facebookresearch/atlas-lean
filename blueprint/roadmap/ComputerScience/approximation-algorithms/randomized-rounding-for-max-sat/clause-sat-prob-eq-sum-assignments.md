# The closed form is the satisfaction probability

Let `C` be a clause whose literals use
distinct variables, with variable set `V = {l.1 : l ∈ C}`, and set each variable `i ∈ V` true
independently with probability `p i ∈ [0, 1]`, so that an assignment `a : V → Bool` has
probability
`∏_{i ∈ V} P[a i]`, `P[true] = p i`, `P[false] = 1 - p i`. Then `clauseSatProb p C` is the total
probability of the assignments that satisfy `C` (Goemans and Williamson, *SIAM J. Discrete
Math.* 7(4) (1994), §2): because the literals use distinct variables, exactly one assignment
falsifies `C`, the one making every literal false, and its probability is
`∏_l (1 - P[l true])`.
