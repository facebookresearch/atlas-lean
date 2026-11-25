# ABC-MCMC is reversible for the tolerance posterior

Use the [ABC model](../rejection-sampling/abc-rejection-target-law-and-zero-tolerance-disc.md)
with prior density $p$ relative to a sigma-finite parameter measure,
proposal density $q(\theta,\theta')$, measurable acceptance event
$A_\varepsilon$, and $Z_\varepsilon>0$.
At a current parameter with $p(\theta)>0$, propose $\theta'$ using $q$
and draw fresh $X'\sim P_{\theta'}$ independently conditional on that
proposal. Accept the proposal with probability

$$\mathbf1_{A_\varepsilon}(X')
 \min\left(1,\frac{p(\theta')q(\theta',\theta)}
 {p(\theta)q(\theta,\theta')}\right),$$

where the ratio factor is one when its denominator is zero; otherwise
retain the current parameter. This parameter-only kernel is reversible
for $\pi_\varepsilon(d\theta)\propto p(\theta)a_\varepsilon(\theta)
\lambda(d\theta)$ on the prior support, and hence invariant.
At infinite tolerance it is MH targeting the prior.

## Depends on

- [Tolerance-conditioned posterior](../rejection-sampling/abc-rejection-target-law-and-zero-tolerance-disc.md)

## Proof depends on

- [Exact pseudo-marginal MH with retained auxiliary state](pseudo-marginal-mh-exactness-with-unbiased-nonne.md)

## Expansion

The nonnegative estimator is $\widehat a(\theta,X)=\mathbf1_{A_\varepsilon}(X)$.
Its mean is $a_\varepsilon(\theta)$. In the extended pseudo-marginal chain,
initialize at accepted auxiliary data and retain them on rejection.
The current indicator is then always one, so the acceptance formula
reduces to the displayed one and depends on no other feature of the
current simulated datum. Therefore the parameter projection is itself
Markov; the old auxiliary datum can be omitted in this special indicator
implementation. This simplification does not permit refreshing the
current likelihood estimate in a general pseudo-marginal method.

One may also verify reversibility directly: off-diagonal accepted flow
is proportional to
$a_\varepsilon(\theta)a_\varepsilon(\theta')
\min(p(\theta)q(\theta,\theta'),p(\theta')q(\theta',\theta))$,
which is symmetric; rejected flow stays on the diagonal.
If $a_\varepsilon=0$ at some parameters they have zero target mass, and
accepted proposals into them occur with probability zero. Normalizability
and reversibility do not imply convergence from every initial state.

## Sources

- P. Marjoram, J. Molitor, V. Plagnol and S. Tavaré, *Markov chain Monte Carlo without likelihoods*, PNAS 100 (2003), 15324–15328, <https://doi.org/10.1073/pnas.0306899100>, bibliographic background only.
- C. Andrieu and G. O. Roberts (2009), <https://doi.org/10.1214/07-AOS574>, <https://arxiv.org/abs/0903.5480>, extended-target argument (2.2), (2.9)–(2.10). Its indicator specialization is derived above.
