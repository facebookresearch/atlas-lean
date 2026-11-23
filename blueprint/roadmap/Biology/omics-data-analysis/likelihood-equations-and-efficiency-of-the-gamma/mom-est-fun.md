# Mom Est Fun

The moment estimating function of one count `k` at `θ = (a, b)`:
`(b k - σ a, b² k² - σ a b - σ² a - σ² a²)`, which is `(b (k - μ), b² (k² - μ - μ² / a - μ²))`
with `μ = σ a / b`. Its sample equations `∑ᵢ momEstFun σ θ kᵢ = 0` say that the sample mean and
second moment match the negative binomial ones, so for overdispersed samples their unique
positive root is the moment estimate (`sum_momEstFun_mom_eq_zero`).
