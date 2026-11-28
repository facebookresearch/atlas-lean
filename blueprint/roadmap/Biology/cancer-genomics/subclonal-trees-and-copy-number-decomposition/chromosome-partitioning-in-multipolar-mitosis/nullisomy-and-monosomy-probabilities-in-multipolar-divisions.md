# Nullisomy and monosomy probabilities in multipolar divisions

Consider a $k$-ploid mother cell ($k \ge 1$ copies of each of $M$ nonhomologous chromosomes) dividing with $p \ge 2$ spindle poles, each pole giving one daughter cell. Model chromatid partitioning as follows: (i) the two sister chromatids of every replicated chromosome go to two **distinct** poles, the unordered pair of poles being uniform among the $\binom{p}{2}$ choices; (ii) different chromatid pairs, both homologous copies and different chromosomes, are partitioned independently. A daughter cell is **nullisomic** for a chromosome if it receives no copy of it and **monosomic** if it receives exactly one.

**Proposition.** For a fixed daughter cell and a fixed chromosome,

$$P(\text{nullisomy}) = \left(\frac{p-2}{p}\right)^{k}, \qquad P(\text{monosomy}) = \frac{2k\,(p-2)^{k-1}}{p^{k}},$$

and the probability of nullisomy or monosomy is $\big((p-2)^k + 2k (p-2)^{k-1}\big)/p^k$. For the whole daughter genome, the number of nullisomic (resp. monosomic) chromosomes is $\mathrm{Bin}(M, q)$ with $q$ the corresponding per-chromosome probability, so

$$P(\text{at least one nullisomy}) = 1 - \left(1 - \left(\frac{p-2}{p}\right)^{k}\right)^{M},$$

and analogously for monosomy and for nullisomy-or-monosomy.

For a bipolar division ($p = 2$) each daughter receives exactly one chromatid of every pair, so nullisomy is impossible for every $k \ge 1$ and monosomy for every $k \ge 2$ (for $k = 1$ it is certain). For a tetraploid cell ($k = 4$, $M = 23$) the per-chromosome nullisomy probability is $1/81$ for $p = 3$ and $1/16$ for $p = 4$, so a given daughter of a tripolar division lacks some chromosome with probability $1 - (80/81)^{23} \approx 0.25$, and a given daughter of a tetrapolar division with probability $1 - (15/16)^{23} \approx 0.77$ (these are per daughter, not per division), which explains the rapid loss of highly aneuploid progeny of multipolar divisions.

## Expansion

A single chromatid pair has $\binom{p}{2}$ equally likely placements, of which $\binom{p-1}{2}$ avoid a given pole; independence over the $k$ homologous pairs gives $\big(\binom{p-1}{2}/\binom{p}{2}\big)^k = ((p-2)/p)^k$. For monosomy, choose which of the $k$ pairs sends one chromatid to the given pole ($k$ ways), which other pole receives its sister ($p-1$ ways), and place the remaining $k-1$ pairs avoiding the pole: $k(p-1)\binom{p-1}{2}^{k-1}/\binom{p}{2}^k = 2k(p-2)^{k-1}/p^k$. Nullisomy and monosomy are disjoint events for one chromosome, and independence across the $M$ chromosomes gives the binomial counts and the complement formula.

## Sources

- N. C. Baudoin, J. M. Nicholson, K. Soto, O. Martin, J. Chen and D. Cimini, "Asymmetric clustering of centrosomes defines the early evolution of tetraploid cells", eLife 9 (2020) e54565, Materials and Methods ("Probabilistic model for karyotypic outcomes of multipolar divisions", Equations 1–11), <https://doi.org/10.7554/elife.54565>, PMCID PMC7250578.
