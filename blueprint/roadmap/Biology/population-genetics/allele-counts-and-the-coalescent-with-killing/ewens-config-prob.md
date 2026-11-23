# Ewens Config Prob

The **Ewens sampling formula** written on an allele-count configuration
`a = (a_1, …, a_n)` (Ewens 1972):
`P(a_1, …, a_n) = n! / (θ (θ + 1) ⋯ (θ + n - 1)) · ∏_{j=1}^n (θ / j) ^ {a_j} / a_j!`.
Only the values `a 1, …, a n` enter. The formula is the probability of the configuration `a`
when `∑_{j=1}^n j a_j = n` (`sum_ewensProb_alleleCount_eq`); otherwise no sample has
configuration `a`.
