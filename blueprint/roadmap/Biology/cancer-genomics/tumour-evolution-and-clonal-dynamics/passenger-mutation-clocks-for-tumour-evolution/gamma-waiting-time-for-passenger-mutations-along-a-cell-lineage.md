# Gamma waiting time for passenger mutations along a cell lineage

**Model.** Follow a single cell lineage forward from tumour initiation. Measure time $s \ge 0$ in cell divisions along the lineage, and assume that neutral (passenger) mutations in the sequenced target arise as a homogeneous Poisson process of rate $r > 0$ per division, where

$$r = u \cdot L,$$

$u$ is the point-mutation rate per base pair per division and $L$ is the number of sequenced base pairs. Mutations present before initiation are neglected.

**Proposition.** Let $S_N$ be the number of divisions until the lineage carries exactly $N \ge 1$ passengers acquired after initiation. Then $S_N$ is the sum of $N$ independent exponential waiting times with mean $1/r$, so

$$S_N \sim \operatorname{Gamma}(\text{shape } N,\ \text{scale } 1/r), \qquad \mathbb E[S_N] = \frac{N}{r}, \qquad \operatorname{sd}(S_N) = \frac{\sqrt N}{r}.$$

If $T_{\mathrm{gen}}$ is the mean time between successive divisions on the lineage, the elapsed time is estimated by

$$T = \frac{T_{\mathrm{gen}}}{r}\bigl(N \pm \sqrt N\bigr).$$

**Application to clonal founding.** If $N_1$ passenger mutations are present in every sample (primary and several metastases) of one patient, they were all carried by a single cell, the founder of the parental clone, and by the preceding argument the interval $T_1$ from initiation to the birth of that founder is estimated with $N = N_1$. The interval $T_2$ from that founder to the founder of an index metastasis uses $N = N_2$, the passengers present in the metastasis but not in the parental clone. For $L = 31.7 \times 10^6$ and $u = 5 \times 10^{-10}$ one gets $r \approx 0.016$ per division.

**Cell-cycle time from labelling indices.** The potential doubling time of a population with S-phase duration $T_s$ and S-phase labelling index $\mathrm{LI}$ is $T_{\mathrm{pot}} = \lambda T_s / \mathrm{LI}$, where $\lambda$ corrects for the non-uniform age distribution of cells through the cycle.

## Expansion

In a Poisson process the inter-arrival times are independent exponentials with mean $1/r$, and the $N$-th arrival time is their sum, which has the Gamma law with shape $N$ and scale $1/r$; its mean and variance are $N/r$ and $N/r^2$. The founder argument is a perfect-phylogeny statement: a mutation shared by all sampled clones lies on the trunk of the tumour phylogeny, so the number of trunk passengers counts divisions on the trunk. The estimate is conservative in the sense that only divisions on one lineage, not total population growth, are measured, and it is only as accurate as the assumed values of $u$ and $T_{\mathrm{gen}}$.

## Sources

- S. Yachida, S. Jones, I. Bozic, T. Antal, R. Leary, B. Fu, M. Kamiyama, R. H. Hruban, J. R. Eshleman, M. A. Nowak, V. E. Velculescu, K. W. Kinzler, B. Vogelstein, C. A. Iacobuzio-Donahue, *Distant metastasis occurs late during the genetic evolution of pancreatic cancer*, Nature 467 (2010), <https://doi.org/10.1038/nature09515>, PMCID PMC3148940. Methods, "Modeling Tumor Evolution" (Gamma law, $r = 31.7\cdot10^6\cdot5\cdot10^{-10}$, $T_{\mathrm{pot}}=\lambda T_s/\mathrm{LI}$ and $T_1 = (T_{\mathrm{gen}}/r)(N_1 \pm \sqrt{N_1})$).
