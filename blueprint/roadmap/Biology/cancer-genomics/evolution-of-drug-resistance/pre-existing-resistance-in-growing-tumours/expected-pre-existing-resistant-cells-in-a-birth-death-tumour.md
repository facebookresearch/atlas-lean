# Expected number of pre-existing resistant cells in a birth–death tumour

Consider a linear birth–death process started from one drug-sensitive cell at time $0$. Every cell divides at rate $b$ and dies at rate $d$, with net growth rate $r = b - d > 0$. Each division of a sensitive cell independently produces one resistant daughter with probability $u$, small enough that its effect on the growth of the sensitive population is negligible ($u \ll 1$); before treatment, resistant cells have the same rates $b$ and $d$ and never revert. Let $S(t)$ and $R(t)$ be the numbers of sensitive and resistant cells. Then $\mathbb E[S(t)] = e^{rt}$ and

$$\mathbb E[R(t)] = \int_0^t u\,b\,e^{rs}\,e^{r(t-s)}\,ds = u\,b\,t\,e^{rt}.$$

At the time $T = (\ln M)/r$ at which the expected sensitive population equals $M$,

$$\mathbb E[R(T)] = \frac{u\,b\,M \ln M}{b - d} = \frac{u\,M \ln M}{1 - d/b}.$$

The expected resistant burden at detection is therefore larger than the naive estimate $uM$ by the factor $\ln M/(1 - d/b)$: mutations that arise early found large clones, and cell death increases the number of divisions needed to reach size $M$.

## Depends on

- [Mean population size of the linear birth–death process](../../../../Probability/branching-processes/linear-birth-death-process/has-sum-mul-prob.md)

## Expansion

The forward equation of the linear birth–death process gives $\frac{d}{dt}\mathbb E[S] = (b - d)\mathbb E[S]$, hence $\mathbb E[S(t)] = e^{rt}$. Resistant cells are created at expected rate $u b\,\mathbb E[S(s)]$, and each resistant cell present at time $s$ has expected progeny $e^{r(t-s)}$ at time $t$, which gives the integral. With $d = 0$ this is the mean of the Lea–Coulson (Luria–Delbrück) model of mutants in an exponentially growing culture, $\mathbb E[R] \approx uM\ln M$; the factor $b/(b-d)$ is the correction for cell death studied by Iwasa, Nowak and Michor. Diaz et al. used this birth–death framework with $b \approx 0.25$ and $d \approx 0.18$ per day (net growth $0.069$, estimated from circulating tumour DNA kinetics) to reject, for each of 16 lesions, the hypothesis that the KRAS mutations detected during anti-EGFR therapy were absent at its start, and estimated that a lesion of $10^9$ cells is expected to carry about $3{,}200$ cells resistant through mutation at one of 42 candidate nucleotides; with a per-site mutation rate of order $10^{-9}$ per division the formula above gives a value of this order.

## Sources

- L. A. Diaz Jr, R. T. Williams, J. Wu, et al., "The molecular evolution of acquired resistance to targeted EGFR blockade in colorectal cancers", Nature 486 (2012), 537–540, <https://doi.org/10.1038/nature11219> (PMC3436069), main text on mathematical modelling of pre-existing KRAS mutations.
- Y. Iwasa, M. A. Nowak, F. Michor, "Evolution of resistance during clonal expansion", Genetics 172 (2006), 2557–2566, <https://doi.org/10.1534/genetics.105.049791>.
