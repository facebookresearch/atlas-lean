# Diamond insulation score and boundary prominence

Let $A$ be a contact matrix over genomic bins and $w \ge 1$ a window size in bins. The insulation
score of bin $k$ is the average contact frequency across $k$ within a diamond-shaped window on the
diagonal, that is, over pairs with one bin upstream and one downstream of $k$ within distance
$w$; one standard choice is

$$I_w(k) = \operatorname{mean}\{A_{ij} : k - w < i \le k,\ k < j \le k + w,\ i, j \text{ valid}\},$$

usually reported as $\log_2$ of $I_w(k)$ divided by its genome-wide median. Insulating boundaries
are the local minima of $k \mapsto I_w(k)$, and the strength of a boundary is its topographic
prominence: the depth of the minimum below the lower of the two highest values reached before the
profile descends below the minimum on either side. Strong boundaries are selected by thresholding
prominences with an automatic histogram threshold (for example Li or Otsu).

## Depends on

- [Contact-probability scaling and observed-over-expected maps](contact-probability-scaling-and-observed-over-expected-maps.md)

## Expansion

Inside a contact domain, loci on both sides of a bin contact each other often, so the diamond
average is high; at a domain edge, contacts between the upstream and downstream sides are
depleted and the score dips. Averaging over a window makes the profile robust to sequencing depth,
and the window size selects the scale of the domains detected. Random fluctuations create many
shallow minima, which prominence filters out because prominence measures how far a minimum stands
out from its surroundings rather than its absolute value.

## Sources

- Open2C, N. Abdennur, S. Abraham, G. Fudenberg, I. M. Flyamer, A. A. Galitsyna, A. Goloborodko,
  M. Imakaev, B. A. Oksuz, S. V. Venev, Y. Xiao, et al., "Cooltools: enabling high-resolution Hi-C
  analysis in Python", PLoS Computational Biology 20 (2024) e1012067, Results, "Insulation and
  boundaries", <https://doi.org/10.1371/journal.pcbi.1012067> (PMC11098495).
