# Products of measures with densities

Let $\mu_i$, for $i$ in a finite index set, be $\sigma$-finite measures on measurable spaces $X_i$,
and $f_i : X_i \to [0, \infty]$ measurable functions such that each measure $f_i \mu_i$ with
density $f_i$ is $\sigma$-finite. Then the product of the measures $f_i \mu_i$ is the measure with
density $y \mapsto \prod_i f_i(y_i)$ with respect to the product of the $\mu_i$.

## Idea

Both sides are measures on the product space, so it is enough to compare them on boxes
$\prod_i A_i$, which form a $\pi$-system generating the product $\sigma$-algebra; the
$\sigma$-finiteness hypotheses make a measure on the product determined by its values on boxes.
On a box the left side gives $\prod_i \int_{A_i} f_i \, d\mu_i$, and Tonelli's theorem for a
product of one-variable functions gives the same value for the right side. In probability this is
the statement that independent random variables with densities have the product density, as for
the standard Gaussian on $\mathbb{R}^n$.

## Statements

- [A product of measures with densities](pi-with-density.md)
- [Tonelli for products](lintegral-fintype-prod-eq-prod.md): used to compare the two sides on boxes.
- [Iterated integrals of a product of one-variable functions](lmarginal-prod.md): the same computation, one coordinate at a time.
