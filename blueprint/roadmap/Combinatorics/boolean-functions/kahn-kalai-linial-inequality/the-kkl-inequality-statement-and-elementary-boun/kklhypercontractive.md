# KKL inequality with constant $c$ for the $p$-biased measure

The KKL inequality with constant `c` for the Bernoulli(`p`) product measure: for every finite
 nonempty index type `E` and every Boolean function `φ` on `{0, 1}^E`, `c · Var(φ) · log (1 /
 maxₑ Infₑ(φ)) ≤ ∑ₑ Infₑ(φ)`, with `Infₑ(φ)` the probability that `e` is pivotal.

Despite its name, this is the conclusion of the KKL theorem, not a hypercontractivity estimate.
 It holds trivially for `c = 0` (`kkl_hypercontractive_zero`) and is proved for `p = 1/2`, `c =
 2` in `fsr_pbiased_endpoint`. When `maxₑ Infₑ(φ) = 0`, `log (1 / 0) = 0` in Lean and the
 inequality is trivial.
