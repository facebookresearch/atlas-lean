# Swap omniprediction, swap multicalibration and swap agnostic learning are equivalent

For every bounded class $\mathcal{C}$ ($|c(x)| \le 1$) that is closed under negation and contains the constant functions $0$ and $1$, the following are equivalent up to polynomial changes of the error parameter: $(\mathcal{C}, \alpha)$-swap multicalibration; being a swap omnipredictor for the $B$-nice convex losses (convex, $1$-Lipschitz on an interval containing their optimal actions, with $|\ell(t,1) - \ell(t,0)| \le B$ there) against linear combinations $\mathrm{Lin}(\mathcal{C}, W)$, with error $O((W + B)\alpha)$, for all $W \ge 1$, $B \ge 0$; and swap agnostic learning for the squared loss alone against $\mathrm{Lin}(\mathcal{C}, 2)$. In particular swap agnostic learning for every nice convex loss follows. The closure assumptions cannot be dropped: for $\mathcal{C} = \{0\}$ every swap multicalibration test vanishes, yet the constant predictor $p \equiv 1$ when $y = 0$ always is not a swap agnostic learner for the squared loss against $\mathrm{Lin}(\mathcal{C}, 2) = \{0\}$, since it has loss $1$ while the hypothesis $0$ has loss $0$. Moreover swap multicalibration is essentially equivalent to standard multicalibration: known multicalibration algorithms already output swap multicalibrated predictors, and discretizing a multicalibrated predictor gives a nearby swap multicalibrated one; so existing algorithms achieve all three notions. Swap loss OI for a family of nice losses containing the squared loss is equivalent to swap multicalibration for $\partial\mathcal{L} \circ \mathcal{C}$, while loss OI and swap omniprediction are incomparable. In particular multigroup fairness in the form of multicalibration is necessary, not merely sufficient, for the swap variant of omniprediction, and a single notion of outcome indistinguishability captures all existing notions of omniprediction and multicalibration.

## Proof sketch

Swap multicalibration implies swap omniprediction by applying the omniprediction argument separately on each level set with its own $c_v$. Swap omniprediction gives swap agnostic learning for the squared loss by fixing the loss. Conversely, if on a level set $\{p = v\}$ some $c$ has correlation $\beta$ with $y - v$, then the hypothesis $v + \beta c \in \mathrm{Lin}(\mathcal{C}, 2)$ (the constants are in the span because $1 \in \mathcal{C}$ and $\mathcal{C}$ is closed under negation) improves the squared loss there by about $\beta^2$; summed over level sets this contradicts swap agnostic learning for the squared loss, which shows necessity.

## Depends on

- [Swap agnostic learning and swap omniprediction](swap-agnostic-learning.md)
- [Omnipredictors](omnipredictor.md)
- [Multicalibrated predictors](../multicalibration-and-multiaccuracy/multicalibrated-predictor.md)
- [Outcome indistinguishability and its access hierarchy](outcome-indistinguishability.md)

## Proof depends on

- [Multicalibration implies omniprediction for convex Lipschitz losses](multicalibration-implies-omniprediction.md)

## Sources

- P. Gopalan, M. P. Kim, O. Reingold, "Swap Agnostic Learning, or Characterizing Omniprediction via Multicalibration", NeurIPS (2023), arXiv:2302.06726, Section 4 (standing assumptions on $\mathcal{C}$), Theorems 4.3 and 5.1, Theorem 3 (incomparability), Section 3.
