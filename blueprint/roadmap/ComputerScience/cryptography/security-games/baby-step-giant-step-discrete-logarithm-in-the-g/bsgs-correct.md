# Baby-step giant-step returns the discrete logarithm

Let $q > 1$ and let $\mathrm{enc}$ be a permutation of $\mathbb{Z}/q$, the encoding of exponents as labels, with oracle $\mathrm{enc}(a), \mathrm{enc}(b) \mapsto \mathrm{enc}(a + b)$ for multiplication and $\mathrm{enc}(a) \mapsto \mathrm{enc}(-a)$ for inversion. For every $x \in \mathbb{Z}/q$, running the [baby-step giant-step algorithm](bsgs.md) against this oracle on the identity label $\mathrm{enc}(0)$, the generator label $\mathrm{enc}(1)$ and the target label $\mathrm{enc}(x)$ returns $\mathrm{some}\ x$.

The statement is for these three labels under the oracle of the same permutation, not for arbitrary supplied labels or oracles.
