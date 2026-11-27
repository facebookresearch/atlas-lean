# Oracle inequalities for the Gibbs posterior

Let $\Theta$ be a measurable space, $\ell : \Theta \times Z \to [0,1]$ jointly measurable, $P$ a prior probability measure, $m \ge 1$, $\lambda > 0$ and $\delta > 0$. For a sample $S$ let $\hat{Q}_S$ be the Gibbs posterior, $d\hat{Q}_S/dP \propto e^{-\lambda L_S(\theta)}$. With probability at least $1 - \delta$ over $S \sim D^m$, simultaneously for every probability measure $Q$ with $\mathrm{KL}(Q\,\|\,P) < \infty$,

$$
\mathbb{E}_{\hat{Q}_S} L_D \le \mathbb{E}_Q L_D + \frac{2\,\mathrm{KL}(Q\,\|\,P)}{\lambda} + \frac{\lambda}{4m} + \frac{2\ln(2/\delta)}{\lambda}.
$$

For a comparator $Q$ fixed before the sample the factor $2$ on $\mathrm{KL}(Q\,\|\,P)$ improves to $1$.

## Proof sketch

Apply the linear PAC-Bayes-Hoeffding bound in both directions at confidence $\delta/2$: the upper tail bounds $\mathbb{E}_{\hat Q} L_D$ by $\mathbb{E}_{\hat Q} L_S + (\mathrm{KL}(\hat Q\|P) + \ln(2/\delta))/\lambda + \lambda/(8m)$. The Gibbs variational principle says $\hat Q$ minimizes $\mathbb{E}_Q L_S + \mathrm{KL}(Q\|P)/\lambda$, and the lower tail bounds $\mathbb{E}_Q L_S$ by $\mathbb{E}_Q L_D$ plus the same terms. For fixed $Q$ the lower tail can use $Q$ itself as prior.

## Depends on

- [Gibbs variational principle](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/is-greatest-integral-sub-kl-div.md)
- [Catoni's PAC-Bayes bound](../catoni-pac-bayes.md)

## Proof depends on

- [Gibbs variational principle](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/is-greatest-integral-sub-kl-div.md)
- [Catoni's PAC-Bayes bound](../catoni-pac-bayes.md)

## Sources

- P. Alquier, "User-friendly Introduction to PAC-Bayes Bounds", Foundations and Trends in Machine Learning, 2024.
- O. Catoni, "PAC-Bayesian Supervised Classification: The Thermodynamics of Statistical Learning", Institute of Mathematical Statistics, 2007.
