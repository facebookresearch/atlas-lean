# Extended haplotype homozygosity (EHH)

For a haplotype sample $h$, a finite set $C$ of haplotypes and a radius $d$, the extended haplotype homozygosity is

$$\mathrm{EHH}_C(d) = \frac{N_C(d)}{|C|\,(|C| - 1)},$$

where $N_C(d)$ is the number of [concordant pairs](concordant-pairs.md), with the convention $x/0 = 0$ (so $\mathrm{EHH}_C(d) = 0$ when $|C| \le 1$). For $|C| \ge 2$ it is the probability that two haplotypes drawn from $C$ without replacement agree at the $d$ sites nearest the core (Sabeti et al. 2002).

## Sources

- P. C. Sabeti, D. E. Reich, J. M. Higgins, H. Z. P. Levine, D. J. Richter, S. F. Schaffner, S. B. Gabriel, J. V. Platko, N. J. Patterson, G. J. McDonald, H. C. Ackerman, S. J. Campbell, D. Altshuler, R. Cooper, D. Kwiatkowski, R. Ward and E. S. Lander, *Detecting recent positive selection in the human genome from haplotype structure*, Nature 419 (2002), 832–837.
