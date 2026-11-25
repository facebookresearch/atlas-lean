# Effective population size with separate sexes

In a diploid population with $N_f \ge 1$ females and $N_m \ge 1$ males in each generation (integers), let
each of at least two offspring have a mother chosen uniformly among the females and a father chosen
uniformly among the males, independently of all other offspring, and receive from each parent one of the
parent's two gene copies with probability $1/2$ each, independently (Mendelian transmission at an
autosomal locus). Take one gene copy at random from each of two distinct
offspring. The probability that both are copies of the same gene of the parental generation is exactly

$$c = \frac{1}{8}\Bigl(\frac{1}{N_f} + \frac{1}{N_m}\Bigr):$$

with probability $1/4$ both copies are maternal, and they then come from the same mother with
probability $1/N_f$ and from the same gene of that mother with probability $1/2$; likewise for paternal
copies; a maternal and a paternal copy never come from the same gene. Defining the effective size by
$c = 1/(2N^*)$, as for a Wright–Fisher population of $N^*$ diploids, gives

$$N^* = \frac{4 N_f N_m}{N_f + N_m} .$$

Since $4 N_f N_m \le (N_f + N_m)^2$, $N^* \le N_f + N_m$, with equality if and only if $N_f = N_m$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.6, "Separate sexes", equations (VI-32)–(VI-36), pp. 266–267.
