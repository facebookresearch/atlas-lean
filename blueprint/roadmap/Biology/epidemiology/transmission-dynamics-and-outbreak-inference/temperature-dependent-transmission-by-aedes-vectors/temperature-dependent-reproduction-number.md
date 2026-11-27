# Temperature-dependent reproduction number for a mosquito-borne virus

In a Ross-Macdonald model of vector-borne transmission in which every vector and pathogen trait is a function of temperature $T$, the basic reproduction number is

$$R_0(T) = \left( \frac{a(T)^2\, b(T)\, c(T)\, e^{-\mu(T)/\mathrm{PDR}(T)}\, \mathrm{EFD}(T)\, p_{EA}(T)\, \mathrm{MDR}(T)}{N\, r\, \mu(T)^3} \right)^{1/2},$$

where $a$ is the per-mosquito biting rate, $bc$ the vector competence, $\mu$ the adult mosquito mortality rate, $\mathrm{PDR}$ the pathogen development rate inside the vector, $\mathrm{EFD}$ eggs per female per day, $\mathrm{MDR}$ the egg-to-adult development rate, $p_{EA}$ the egg-to-adult survival probability, $N$ the human population size and $r$ the human recovery rate. Since $N$ and $r$ do not depend on $T$, the function $T \mapsto R_0(T)$ is determined up to a positive constant, and is reported rescaled to $[0,1]$; temperatures with $R_0(T) > 0$ are those at which temperature does not by itself preclude transmission.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Remarks

The square root reflects the two-host cycle: one generation of the next-generation operator takes human to mosquito and mosquito to human, so $R_0$ is the geometric mean of the two half-cycles, which is why the biting rate enters squared and the competence as the product $bc$ of the two directions. The factor $e^{-\mu/\mathrm{PDR}}$ is the probability that a mosquito survives the extrinsic incubation period, an exponential survival over a mean duration $1/\mathrm{PDR}$; the $\mu^{-3}$ collects adult lifespan appearing once per infectious period and twice through the equilibrium vector population sustained by $\mathrm{EFD}\, p_{EA}\, \mathrm{MDR}$. Each trait has a unimodal thermal response, and the support of the product is the intersection of the trait supports, so it is no wider than the support of any single trait and the thermal window for transmission is set by whichever trait fails first at each end: mortality at the hot end, development at the cold end.

## Sources

- Ryan SJ, Carlson CJ, Mordecai EA, Johnson LR. Global expansion and redistribution of Aedes-borne virus transmission risk with climate change. *PLOS Neglected Tropical Diseases* 13:e0007213 (2019), "The temperature dependent $R_0$ model". DOI <https://doi.org/10.1371/journal.pntd.0007213>. PMCID PMC6438455.
- Mordecai EA, Cohen JM, Evans MV, et al. Detecting the impact of temperature on transmission of Zika, dengue, and chikungunya using mechanistic models. *PLOS Neglected Tropical Diseases* 11:e0005568 (2017). DOI <https://doi.org/10.1371/journal.pntd.0005568>.
