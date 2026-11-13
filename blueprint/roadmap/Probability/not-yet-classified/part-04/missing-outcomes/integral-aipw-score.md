# Double robustness of the AIPW score with missing outcomes

**Double robustness of the AIPW score with missing outcomes** (Robins, Rotnitzky & Zhao
1994; Bang & Robins 2005): for a covariate with finitely many values, under missing at random
and positivity of the response, `E[m(X) + 1_R (Y - m(X)) / π(X)] = E[Y]` when **either** the
response propensity is correct (`π(x) = P(R | X = x)`) **or** the outcome regression is correct
(`m(x) = E[Y | X = x]`), on every covariate value of positive probability. The nuisances are
fixed functions.
