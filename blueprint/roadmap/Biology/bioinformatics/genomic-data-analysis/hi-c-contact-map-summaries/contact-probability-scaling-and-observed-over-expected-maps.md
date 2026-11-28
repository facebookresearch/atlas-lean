# Contact-probability scaling and observed-over-expected maps

Let $A = (A_{ij})$ be a symmetric (balanced or raw) contact matrix over genomic bins of a region,
and let $V$ be the set of valid (unfiltered) bins. For a separation $s \ge 0$ in bins, the expected
contact frequency (contact-probability scaling) is the mean over valid pairs at that separation,

$$P(s) = \frac{1}{\#\{(i,j) : i, j \in V,\ j - i = s\}} \sum_{\substack{i,j \in V\\ j-i = s}} A_{ij},$$

and its local slope on log–log axes is $\dfrac{d \log P}{d \log s}$, estimated after smoothing
$P(s)$ in log space. The observed-over-expected map is

$$\tilde A_{ij} = \frac{A_{ij}}{P(|i - j|)} .$$

The cis compartment profile is the leading eigenvector (or another selected eigenvector) of the
observed-over-expected matrix of a chromosome, with its sign and order fixed by correlation with
a phasing track such as GC content. Given an assignment of bins to classes $1, \dots, Q$ (for
example by quantiles of the compartment profile), the saddle summary is the $Q \times Q$ matrix

$$S_{pq} = \operatorname{mean}\{\tilde A_{ij} : i \in p,\ j \in q\}.$$

## Expansion

Contact frequency falls steeply with genomic separation because a chromosome is a long polymer;
the slope of $P(s)$ at a given scale reflects folding at that scale and changes with the cell
cycle and with loop-extruding complexes. Counting only valid pairs at each separation keeps
filtered bins from biasing the mean. Dividing by $P(s)$ removes the polymer trend so that
locus-specific features, notably the plaid pattern of active and inactive compartments, dominate
the matrix; the leading eigenvector of that matrix then separates the two compartment types, but
an eigenvector is defined only up to sign, hence the phasing track. In a saddle summary, enrichment
in the same-class corners relative to the opposite-class corners quantifies compartment strength.

## Sources

- Open2C, N. Abdennur, S. Abraham, G. Fudenberg, I. M. Flyamer, A. A. Galitsyna, A. Goloborodko,
  M. Imakaev, B. A. Oksuz, S. V. Venev, Y. Xiao, et al., "Cooltools: enabling high-resolution Hi-C
  analysis in Python", PLoS Computational Biology 20 (2024) e1012067, Results,
  "Contacts-vs-distance & expected", "Compartmentalization" and "Pairwise class-averaging &
  saddles", <https://doi.org/10.1371/journal.pcbi.1012067> (PMC11098495).
