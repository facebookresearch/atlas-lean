# KKL inequality for `p`-biased measures

**KKL inequality for `p`-biased measures** (Bourgain–Kahn–Kalai–Katznelson–Linial;
Talagrand). For every `p ∈ (0, 1)` there is `c > 0` such that for every finite nonempty `E` and
every Boolean function `φ` on `{0, 1}^E`,
`c · Var_p(φ) · log (1 / maxₑ Infₑ^p(φ)) ≤ ∑ₑ Infₑ^p(φ)`, where `Infₑ^p(φ)` is the probability
under the Bernoulli(`p`) product measure that `e` is pivotal for `φ`.

Talagrand's inequality `Var_p(φ) ≤ K(p) ∑ₑ Infₑ / log (1 / (p (1 - p) Infₑ))` gives this with
`c = 1 / K(p)`, since each `Infₑ ≤ maxₑ Infₑ`.

## Sources

- M. Talagrand, *On Russo's approximate zero-one law*, Ann. Probab. 22 (1994); J. Bourgain, J. Kahn, G. Kalai, Y. Katznelson, N. Linial, *The influence of variables in product spaces*, Israel J. Math. 77 (1992).
