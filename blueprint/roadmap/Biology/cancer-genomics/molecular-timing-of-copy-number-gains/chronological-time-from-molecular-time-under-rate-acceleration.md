# Chronological time from molecular time under a mutation-rate acceleration

Let clonal point mutations accumulate in a lineage from fertilization ($t = 0$) to diagnosis at age $t_D > 0$ with rate $r(t) > 0$, and let $M(t) = \int_0^t r(u)\, du$. An event at chronological time $t$ has molecular time $T = M(t)/M(t_D) \in [0, 1]$, the fraction of clonal mutations acquired before it (the quantity estimated by the [timing closed form](timing-eq.md)). For a rate $r_0$ that is accelerated by a factor $a \ge 1$ from time $t_a \in [0, t_D]$ on,

$$M(t) = \begin{cases} r_0 t, & t \le t_a, \\ r_0\big(t_a + a(t - t_a)\big), & t \ge t_a, \end{cases}$$

the inverse map from molecular to chronological time is, with $\tau = T\,\big(t_a + a(t_D - t_a)\big)$,

$$t(T) = \begin{cases} \tau, & \tau \le t_a, \\ t_a + (\tau - t_a)/a, & \tau \ge t_a, \end{cases}$$

and $t(T) \ge T\, t_D$, with equality for all $T$ if and only if $a = 1$, $t_a = 0$ or $t_a = t_D$. The acceleration is estimated from tumours sampled at diagnosis (age $t_D$) and relapse after an elapsed interval $t_R > 0$ from diagnosis to relapse as

$$a = \frac{n_R}{n_D} \cdot \frac{t_D}{t_R},$$

where $n_D$ is the number of mutations shared by both samples and $n_R$ the number private to the relapse.

## Depends on

- [The timing closed form](timing-eq.md)

## Expansion

The formula for $t(T)$ inverts the piecewise-linear, strictly increasing $M$ after scaling by $M(t_D) = r_0(t_a + a(t_D - t_a))$. Since $r$ is nondecreasing, $M$ is convex with $M(0) = 0$, so $M(t) \le (t/t_D) M(t_D)$, i.e. $T \le t/t_D$: under acceleration the constant-rate conversion $T\, t_D$ places events too early relative to diagnosis, overstating how long before diagnosis they occurred. Gerstung et al. count CpG>TpG mutations, a clock-like signature, and take typical accelerations of $5\times$ ($2.5\times$ for brain cancers, $7.5\times$ for ovarian cancer); because the onset $t_a$ is unknown, they average over onsets spanning the 15 years before diagnosis by Monte Carlo simulation, treating subclonal mutations as acquired at full acceleration.

## Sources

- M. Gerstung, C. Jolly, I. Leshchiner et al., "The evolutionary history of 2,658 cancers", Nature 578 (2020), 122-128, <https://doi.org/10.1038/s41586-019-1907-7> (PMC7054212). Methods, real-time estimation of whole-genome duplication and the most recent common ancestor.
