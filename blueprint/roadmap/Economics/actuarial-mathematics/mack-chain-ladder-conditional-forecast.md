# Chain-ladder forecast under Mack's conditional-mean assumptions

Let $C_{i,k}$, $0 \le i, k \le n$, be cumulative claims of accident year $i$ after $k$ development periods, observed on the triangle $\mathcal D = \{C_{i,k} : i + k \le n\}$. Assume:

1. accident years are independent: the vectors $(C_{i,0}, \dots, C_{i,n})$, $i = 0, \dots, n$, are independent;
2. there are development factors $f_0, \dots, f_{n-1} > 0$ with $\mathbb E[C_{i,k+1} \mid C_{i,0}, \dots, C_{i,k}] = f_k\, C_{i,k}$ for all $i$ and $k$, and each $C_{i,k}$ is integrable.

Then for every accident year $i$,

$$\mathbb E[C_{i,n} \mid \mathcal D] = C_{i,n-i} \prod_{j=n-i}^{n-1} f_j,$$

with the empty product equal to $1$ for $i = 0$. The chain-ladder completion replaces the unknown $f_j$ by estimated factors; this page states the conditional forecast with known factors.

## Depends on

- [Conditional expectation given a σ-field](../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)
- [Independence of σ-fields, random variables and events](../../Probability/foundations/independent-events-and-random-variables/independence/independence-sigma-fields.md)

## Proof depends on

- [Tower property of conditional expectation](../../Probability/foundations/conditional-expectation/tower-property/tower-property.md)
- [Independence of σ-fields, random variables and events](../../Probability/foundations/independent-events-and-random-variables/independence/independence-sigma-fields.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Conditional expectation is unchanged by adjoining an independent σ-field: if $\sigma(X) \vee \mathcal G$ is independent of $\mathcal H$, then $\mathbb E[X \mid \mathcal G \vee \mathcal H] = \mathbb E[X \mid \mathcal G]$ (proof prerequisite)

## Sources

- T. Mack, "Distribution-free calculation of the standard error of chain ladder reserve estimates", *ASTIN Bulletin* 23(2):213–225, 1993
- M. V. Wüthrich and M. Merz, *Stochastic Claims Reserving Methods in Insurance*, Wiley, 2008, Chapter 3 (the distribution-free chain-ladder model)
