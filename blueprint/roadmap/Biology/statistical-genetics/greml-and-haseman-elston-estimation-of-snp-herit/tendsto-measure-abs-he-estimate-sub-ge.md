# Consistency of Haseman–Elston regression

Consider a sequence of LD-score models
(`y = X β + ε` with the GRM `A = X Xᵀ / M`) on finite measure spaces (in the application,
probability spaces), with `N n` individuals,
`M n` markers and common SNP heritability `h²`. Suppose the phenotype cross-products are square
integrable and their covariance matrix has absolute row sums bounded by a constant `C`
uniformly in `n` (a weak-dependence condition on the pairs; see the module docstring for
family GRMs, where it holds, and unrelated samples, where it probably does not), and the
off-diagonal GRM energy
`∑_{i<j} A_ij²` tends to infinity. Then the HE estimator converges in probability to `h²`:
`μₙ {|ĥ²ₙ - h²| ≥ ε} → 0` for every `ε > 0`.
