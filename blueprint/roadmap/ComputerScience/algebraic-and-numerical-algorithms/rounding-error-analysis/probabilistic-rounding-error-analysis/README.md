# Probabilistic rounding error analysis

Worst-case rounding error bounds grow like $nu$, through the constant $\gamma_n = nu/(1 - nu)$, and are vacuous once $nu \ge 1$, which happens for modest $n$ in half precision. If the rounding errors are independent random variables of mean zero, or more generally each has mean zero conditionally on the earlier ones, a concentration inequality replaces $nu$ by $\lambda\sqrt{n}\,u$ with probability close to $1$; mean zero alone is not enough, since errors that all equal the same random sign times $u$ each have mean zero. Independence is a modelling assumption for round to nearest, but stochastic rounding makes the errors mean independent by construction, which with the bound $|\delta| \le 2u$ (valid when nothing underflows or overflows) is enough for the Azuma–Hoeffding inequality, so the $\sqrt n$ bounds then hold without a modelling assumption.

- [Probabilistic model of rounding errors](probabilistic-model-of-rounding-errors.md)
- [Probabilistic backward error of inner products](probabilistic-backward-error-of-inner-products.md)
- [Stochastic rounding](stochastic-rounding.md)
- [Stochastic rounding is unbiased](stochastic-rounding-is-unbiased.md)
- [Stochastic rounding errors are mean independent](stochastic-rounding-errors-are-mean-independent.md)
- [Probabilistic product bound under mean independence](probabilistic-product-bound-under-mean-independence.md)
- [Inner products under stochastic rounding](inner-products-under-stochastic-rounding.md)

## Related topics

- [The constant γₙ of rounding error analysis](../gamma.md)
- [Azuma's inequality](../../../../Probability/concentration-inequalities/azuma-inequality.md)
