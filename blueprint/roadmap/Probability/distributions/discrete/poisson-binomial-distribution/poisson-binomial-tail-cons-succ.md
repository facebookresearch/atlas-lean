# Poisson-binomial tail after adding a trial

Adding a trial with probability `a` raises the upper tail by exactly `a P(S = k)`:
`P(S' ≥ k + 1) = P(S ≥ k + 1) + a P(S = k)`. So the tail is affine in each trial's probability,
with nonnegative slope a point mass of the remaining trials.
