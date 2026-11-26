# EHH as homozygosity of window-type counts

For every haplotype sample, every finite set $C$ and every radius $d$,

$$\mathrm{EHH}_C(d) = \frac{\sum_{t} c_t (c_t - 1)}{|C|\,(|C| - 1)},$$

where $t$ ranges over the [windows](window.md) of radius $d$ occurring in $C$, $c_t$ is the number of haplotypes of $C$ with window $t$, and $x/0 = 0$.
