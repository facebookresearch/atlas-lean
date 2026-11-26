# Probabilistic model of rounding errors

In the standard model of floating-point arithmetic each elementary operation satisfies $\mathrm{fl}(x \mathbin{op} y) = (x \mathbin{op} y)(1 + \delta)$ with $|\delta| \le u$, the unit roundoff. The *probabilistic model of rounding errors* assumes that, in the computation of interest, the quantities $\delta$ associated with every pair of operands are independent random variables of mean zero. They need not be identically distributed.

The model is not always realistic: some $\delta$ are necessarily zero (exact operations), repeated operand pairs repeat the same $\delta$, and an operand computed earlier makes the new $\delta$ depend on earlier ones.

## Depends on

- [The relative error bound](../../floating-point-rounding/abs-fl-sub-le.md)

## Sources

- N. J. Higham and T. Mary, "A new approach to probabilistic rounding error analysis", *SIAM J. Sci. Comput.* 41(5):A2815–A2835, 2019; MIMS EPrint 2018.33, Section 2, Model 2.1 and the discussion after it. <https://eprints.maths.manchester.ac.uk/2673/1/paper.pdf>
