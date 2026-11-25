# Probability that a neutral lineage stays linked during a deterministic sweep

Let the favored allele follow the [logistic sweep trajectory](sweep-traj.md) $x(t)$, $x' = s x(1 - x)$, from $x(0) = x_0$ to $x(T) = x_T$, with $0 < x_0 < x_T < 1$
and $s > 0$. Trace back from time $T$ a neutral lineage at recombination rate $r$ from the selected site that is on the favored
background, and let it leave that background at the points of a [Poisson point process](../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md) on $[0, T]$ with intensity $r(1 - x(t))\,dt$, the rate of
recombination with a chromosome not carrying the favored allele. Then the probability that it stays on the favored
background back to time $0$ is

$$\exp\Bigl(-r \int_0^T (1 - x(t))\, dt\Bigr) = \Bigl(\frac{x_0}{x_T}\Bigr)^{r/s},$$

because the number of points has the Poisson law with mean $r \int_0^T (1 - x(t))\, dt$ and $(1 - x)\,dt = dx/(s x)$. For a sweep from one copy, $x_0 = 1/(2N)$, to $x_T \to 1$, it tends to $(2N)^{-r/s}$; it equals $1$ when $r = 0$.
The hitchhiking effect thus depends on $r/s$. The complementary probability $1 - (2N)^{-r/s}$ has the form of the
[escape probability](../composite-selection-scores/escape-prob.md) $1 - e^{-\alpha |y - x|}$ used in composite selection scores, with
$\alpha |y - x| = (r/s) \log(2N)$ when $r$ is proportional to the distance $|y - x|$.

## Depends on

- [Logistic trajectory of a selective sweep](sweep-traj.md)
- [Poisson point process with finite intensity](../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md)

## Proof depends on

- [Point counts of a Poisson point process are Poisson](../../../Probability/point-processes/poisson-point-processes/map-apply-eq-poisson-measure.md)

## Related topics

- [Probability of escaping a selective sweep](../composite-selection-scores/escape-prob.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VIII.8, p. 392 (the hitchhiking effect depends almost entirely on the ratio $s/r$; less recombination into the favored haplotype the faster it increases). The probability is derived above.
