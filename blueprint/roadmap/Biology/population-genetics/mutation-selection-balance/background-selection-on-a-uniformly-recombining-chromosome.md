# Background selection on a uniformly recombining chromosome

Consider a randomly mating population at mutation–selection balance under multiplicative fitness, with deleterious mutations so rare that only heterozygous carriers matter. A mutant heterozygote at selected locus $i$ has fitness $1 - t_i$ with $t_i = hs$, the mutant frequency is $q_i \approx u_i/t_i$, and the recombination frequency with a focal neutral site is $r_i$. To the order of these approximations the expected neutral diversity relative to its value $\pi_0$ without selection is

$$\frac{\pi}{\pi_0} \approx \exp\Bigl(-\sum_i \frac{u_i t_i}{(t_i + r_i(1 - t_i))^2}\Bigr) = \exp\Bigl(-\sum_i \frac{u_i}{t_i (1 + p_i)^2}\Bigr), \qquad p_i = \frac{r_i(1-t_i)}{t_i}. \tag{4}$$

Now take a chromosome of map length $M$ Morgans, short enough that double crossovers are negligible, so the map is linear: $r(z) = z$ for a selected site at map distance $z$ from the neutral site. Let all selected sites share $t$, with total diploid deleterious mutation rate $U$ spread uniformly over the chromosome, and let a fraction $P$ of the map lie to the left of the neutral site and $Q = 1 - P$ to the right. Then $\pi/\pi_0 \approx e^{-E}$ with

$$E = \frac{U\,[\,t + 2PQM(1-t)\,]}{2\,[\,t + QM(1-t)\,]\,[\,t + PM(1-t)\,]}. \tag{9}$$

**Regimes.** If $M \ll t$ then $E \approx U/(2t)$, the non-recombining value $\pi/\pi_0 = e^{-U/(2t)}$. If $M \gg t$ and the neutral site is away from the ends ($PQM \gg t$), then $E \approx U/M$, independent of $P$: the reduction depends only on the density of new mutations per map unit. At the end of the chromosome ($P = 0$), $E = U/\{2[t + M(1-t)]\} \approx U/(2M)$, about half the central value $E = U/(2t + M(1-t)) \approx U/M$.

## Proof sketch

Replacing the sum in (4) by an integral over a continuum of selected sites with mutation density $U/(2M)$ per Morgan gives

$$E = \frac{U}{2Mt}\Bigl(\int_0^{PM}\frac{dz}{(1 + z(1-t)/t)^2} + \int_0^{QM}\frac{dz}{(1 + z(1-t)/t)^2}\Bigr).$$

Since $\int_0^{a} dz/(1 + cz)^2 = a/(1 + ca)$ with $c = (1-t)/t$, the two terms are $U P/(2[t + PM(1-t)])$ and $U Q/(2[t + QM(1-t)])$. Putting them over a common denominator and using $P(t + QM(1-t)) + Q(t + PM(1-t)) = t + 2PQM(1-t)$ gives (9). The limits follow by inspection. With no recombination, (4) reduces to $\pi = f_0\pi_0$, the classical fraction of mutation-free gametes. Each selected locus removes linked neutral variants in proportion to how long a mutant lineage survives in heterozygous carriers ($\approx 1/t$) before recombination separates it ($\approx 1/r$), which produces the factor $(t + r(1-t))^{-2}$.

## Proof depends on

- [Background selection reduces the effective size to the mutation-free class](background-selection-deterministic-reduction-fac.md)

## Sources

- M. Nordborg, B. Charlesworth and D. Charlesworth, "The effect of recombination on background selection", Genetical Research (1996), 159–174, Section 2 (equations (3)–(10)), <https://doi.org/10.1017/S0016672300033619>.
