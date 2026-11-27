# No-access OI is multiaccuracy and sample-access OI is multicalibration

For classes of distinguishers $\mathcal{A}$ and correspondingly derived classes of group functions $\mathcal{C}_{\mathcal{A}}$ (and conversely), no-access outcome indistinguishability with respect to $\mathcal{A}$ is equivalent, up to polynomial changes of the error parameter, to multiaccuracy with respect to $\mathcal{C}_{\mathcal{A}}$, and sample-access outcome indistinguishability is equivalent to multicalibration. Precisely, in Dwork et al.'s set formulation with conditional errors on sets of measure at least $\gamma_{\mathcal{C}}$: $(\mathcal{C}_{\mathcal{A}}, \varepsilon/2)$-multiaccuracy implies $(\mathcal{A}, \varepsilon)$-no-access OI, and $(\mathcal{A}_{\mathcal{C}}, \alpha\gamma_{\mathcal{C}})$-no-access OI implies $(\mathcal{C}, \alpha)$-multiaccuracy; for predictors rounded to a grid of width $1/m$, $(\mathcal{A}_{\mathcal{C},m}, \alpha^2\gamma_{\mathcal{C}}/m)$-sample-access OI implies $(\mathcal{C}, \alpha)$-multicalibration, and multicalibration with respect to a derived class implies sample-access OI. The derived classes have essentially the complexity of the original ones. Consequently both levels can be achieved by the multicalibration algorithms: for distinguishers computed by circuits of size $s$ there are no-access and sample-access OI predictors of circuit size $O(s/\varepsilon^2)$.

## Proof sketch

A binary distinguisher $A(x, y)$ has advantage $\mathbb{E}[(A(x,1) - A(x,0))(y - p(x))]$, which is a multiaccuracy test for $c(x) = A(x,1) - A(x,0)$; conversely each $c$ yields a distinguisher. With sample access, distinguishers can additionally condition on the value $p(x)$, which turns the tests into $c(x)\,\phi(p(x))$ for arbitrary $\phi$, and summing over level sets gives exactly the multicalibration condition.

## Depends on

- [Outcome indistinguishability and its access hierarchy](outcome-indistinguishability.md)
- [Multiaccurate predictors](../multicalibration-and-multiaccuracy/multiaccurate-predictor.md)
- [Multicalibrated predictors](../multicalibration-and-multiaccuracy/multicalibrated-predictor.md)

## Sources

- C. Dwork, M. P. Kim, O. Reingold, G. N. Rothblum, G. Yona, "Outcome Indistinguishability", STOC (2021), arXiv:2011.13426, Theorems 2, 4.3 and 4.4.
