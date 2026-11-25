# Importance sampling of coalescent histories is unbiased for the likelihood

Let $\mathcal H$ be a finite or countable set of genealogical histories, and for a parameter $\theta$ let $P_\theta$ be a joint law of a history $H$ and data $D$ under a coalescent-with-mutation model. For observed data $D$ the likelihood is

$$L(\theta)=\sum_{H\in\mathcal H}P_\theta(D\mid H)\,P_\theta(H)=\sum_{H\in\mathcal H}P_\theta(D,H).$$

Let $Q$ be a proposal law on $\mathcal H$ with $Q(H)>0$ whenever $P_\theta(D,H)>0$. Then the importance weight

$$\widehat L(H)=\frac{P_\theta(D,H)}{Q(H)},\qquad H\sim Q,$$

satisfies $\mathbb E_Q\widehat L=L(\theta)$, so the average of $n$ independent weights is unbiased for $L(\theta)$ for every $n\ge1$. If $L(\theta)>0$, the proposal $Q(H)=P_\theta(H\mid D)$ gives $\widehat L\equiv L(\theta)$ $Q$-almost surely, an estimator of variance zero. The proposals of Griffiths and Tavaré and of Stephens and Donnelly are proposals of this kind on histories that end in the observed sample.

## Proof depends on

- [Change of measure for importance weights](integral-weight-mul.md)
- [The number of segregating sites is conditionally Poisson](../../../../Biology/coalescent-theory/poisson-mutation-on-the-kingman-genealogy/has-cond-distrib-seg-sites-of-mutation.md)

## Expansion

The proof is the [change of measure for importance weights](integral-weight-mul.md) on the countable space $\mathcal H$: summing $Q(H)\,P_\theta(D,H)/Q(H)$ over the support of $Q$ recovers every term with $P_\theta(D,H)>0$. A full page should also

- prove the zero-variance identity and that $P_\theta(\cdot\mid D)$ is the only proposal with zero variance among those satisfying the support condition;
- record that $\widehat L$ is a nonnegative unbiased likelihood estimator, the input of [pseudo-marginal Metropolis–Hastings](pseudo-marginal-mh-exactness-with-unbiased-nonne.md).

## Sources

- M. Stephens and P. Donnelly, *Inference in molecular population genetics*, J. R. Stat. Soc. B 62 (2000), 605–635, <https://ideas.repec.org/a/bla/jorssb/v62y2000i4p605-635.html>, importance sampling in coalescent inference.
- R. C. Griffiths and S. Tavaré, *Simulating probability distributions in the coalescent* (1994), Griffiths–Tavaré proposal.
