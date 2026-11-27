# Robust Le Cam-Birgé test with clipped likelihood-ratio weights

Let $q_0, q_1$ be distributions on a finite set $X$ and define the clipped weight $\beta(x) = \sqrt{(q_0(x) + 2q_1(x))/(2q_0(x) + q_1(x))}$ (and $\beta(x) = 1$ when $q_0(x) = q_1(x) = 0$), which always lies in $[1/\sqrt2, \sqrt2]$. The *Le Cam-Birgé test* favors $q_0$ iff $\prod_{i=1}^n \beta(x_i) < 1$. If $x_1, \dots, x_n$ are i.i.d. from an arbitrary $p$ with $10\,h(p, q_0) \le h(q_0, q_1)$ ($h$ the Hellinger distance, $h^2 = 1 - \mathrm{BC}$), then

$$
\Pr[\text{the test favors } q_1] \le \exp\bigl(-n\,h^2(q_0,q_1)/25\bigr).
$$

In particular, if $h(p, q_0) \le r$ and $10r \le h(q_0,q_1)$, the error is at most $e^{-4nr^2}$. The symmetric statement holds with the roles of $q_0$ and $q_1$ exchanged.

## Proof sketch

The key drift bound is $\sum_x p(x)\beta(x) \le 1 - h^2(q_0,q_1)/25$ whenever $10\,h(p,q_0) \le h(q_0,q_1)$: at $p = q_0$ the mean of $\beta$ falls below $1$ by a constant times $h^2(q_0,q_1)$, and boundedness of $\beta$ makes this stable under Hellinger perturbations of $p$. Markov's inequality on the product and independence give $(1 - h^2/25)^n \le e^{-nh^2/25}$.

## Depends on

- [Hellinger distance](../../../convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Proof depends on

- [Hellinger distance](../../../convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- Lucien Le Cam, "Convergence of Estimates Under Dimensionality Restrictions", The Annals of Statistics 1(1), 1973.
- Lucien Birgé, "Approximation dans les espaces métriques et théorie de l'estimation", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete 65, 1983.
