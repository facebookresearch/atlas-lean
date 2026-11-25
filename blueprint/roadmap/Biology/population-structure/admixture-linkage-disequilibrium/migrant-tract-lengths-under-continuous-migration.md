# Tract-count versus genomic-position weighting in an exponential mixture

Fix $0<a<1$ and let $\nu$ be a probability measure on ages/exposures
$g\in(0,\infty)$ with $0<\int g\,\nu(dg)<\infty$.
Put $\lambda(g)=(1-a)g$ and $Z=\int\lambda(g)\,\nu(dg)$.
Consider an explicit marked-tract mixture model: conditional on tract
mark $g$, a **count-sampled** migrant tract has exponential length of
rate $\lambda(g)$, and $\nu$ is the mark distribution seen by sampling
a genomic position conditional on migrant ancestry. Position sampling
means length bias relative to tract-count sampling in a stationary
collection of tracts of positive intensity. Then the
count-sampled mark law and length density must be

$$\widetilde\nu(dg)=\frac{\lambda(g)}Z\nu(dg),\qquad
 f(\ell)=\int\lambda(g)e^{-\lambda(g)\ell}\widetilde\nu(dg),
 \quad\ell>0.$$

Conversely these formulas define a normalized count-sampled mixture
with mean length $1/Z$ and position-sampled mark law $\nu$.
The position-sampled containing-tract density is

$$f_{\rm pos}(\ell)=Z\ell f(\ell)
 =\int\lambda(g)^2\ell e^{-\lambda(g)\ell}\nu(dg).$$

Thus conditional on its position-sampled mark, the containing tract is
Gamma$(2,\text{rate }\lambda(g))$, not exponential.

## Depends on

- [Count-sampled and position-sampled single-pulse tract laws](tract-length-law-in-the-poisson-switch-model.md)

## Expansion

Length bias multiplies a count-sampled mark's weight by its mean tract
length $1/\lambda(g)$. Consequently the position weight is proportional
to $\widetilde\nu(dg)/\lambda(g)$, which gives the normalized formulas.
Tonelli gives $\int f=1$, $\int\ell f=1/Z$ and $\int f_{\rm pos}=1$.
The finite positive normalizer is necessary; a probability law of ages
alone does not guarantee it. For a single pulse $\nu=\delta_T$, the
count law is Exp$((1-a)T)$ and the position law is Gamma$(2,(1-a)T)$.
With $a=1/2,T=10$, their means are $0.2$ and $0.4$ Morgans respectively.
Candidate breakpoint-segment lengths within a fixed-$g$ relabeling model
have rate $g$, not the maximal-tract rate $(1-a)g$.

This is a conditional exponential-mixture model, **not a derivation of
general continuous migration from age labels alone**. It assumes each
tract has a fixed mixture mark. Gravel's general migration model uses
states $(\text{ancestry},\text{arrival time})$ and may move between
arrival-time states without ending an ancestry tract. Its ancestry-tract
law is a grouped-state excursion law and requires the full transition
matrix; the age-indexed rates $g(1-a)$ above cannot simply be read off
from the rate to the next recombination. A migration-arrival distribution,
a candidate-segment count distribution and a migrant-position distribution
are not interchangeable. That full migration-model derivation remains a
separate problem.

## Sources

- S. Gravel, *Population genetics models of local ancestry* (2012), <https://doi.org/10.1534/genetics.112.139808>, <https://arxiv.org/abs/1202.4811>, general incoming migration, equation (2), and grouped-state excursion discussion, pp. 11–12. The mixture identities here are derived under the additional, explicit model assumptions, not attributed to the general migration model.
