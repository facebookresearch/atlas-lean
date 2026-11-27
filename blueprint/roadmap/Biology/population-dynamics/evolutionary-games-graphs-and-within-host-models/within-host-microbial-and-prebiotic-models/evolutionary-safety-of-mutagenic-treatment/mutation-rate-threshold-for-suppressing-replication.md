# Mutation rate threshold for suppressing replication

In the within-host model of a virus with replication rate $b$, clearance rate $a$, fidelity
$q = 1 - u$ and $m$ positions that are lethal when mutated, the total virus grows exponentially if
$b q^{\,m} > a$ and declines if $b q^{\,m} < a$. A mutagenic treatment that raises the mutation
rate to $u_1$ therefore prevents exponential expansion exactly when $b (1 - u_1)^m < a$, that is
when

$$m \log\frac{1}{1 - u_1} \ >\ \log\frac{b}{a},
\qquad \text{approximately} \qquad u_1 \ >\ \frac{\log(b/a)}{m}
\quad (u_1 \ll 1).$$

The error threshold of the untreated virus is the mutation rate $u_e$ solving
$b\,(1 - u_e)^m = a$.

## Depends on

- [Wild-type and mutant dynamics under mutagenesis](wild-type-and-mutant-dynamics-under-mutagenesis.md)

## Proof sketch

The condition is Eigen's error threshold applied to the viable-genome fraction: replication
survives only while the probability $q^m$ that none of the $m$ essential positions mutates exceeds
the clearance-to-birth ratio $a/b$. The approximation uses $\log(1/(1-u)) \approx u$ for small
$u$. A drug that clears this threshold is evolutionarily safe for free, because the viral
population cannot expand at all; a weaker drug only reduces virus load, and then the mutant output
has to be compared with the untreated case.

## Sources

- G. Lobinska, Y. Pilpel, M. A. Nowak, "Evolutionary safety of lethal mutagenesis driven by antiviral
  treatment", PLoS Biology 21 (2023) e3002214, Eq. (24),
  <https://doi.org/10.1371/journal.pbio.3002214> (PMC10409280).
