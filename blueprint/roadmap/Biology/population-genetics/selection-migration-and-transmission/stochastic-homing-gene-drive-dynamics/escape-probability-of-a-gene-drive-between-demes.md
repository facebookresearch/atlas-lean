# Escape probability of a self-limiting gene drive between demes

Consider $n$ demes of $N$ diploid individuals each, running the [homing-drive Moran model](moran-model-of-a-homing-gene-drive-with-resistance.md) within demes. At each step a migration event (one uniformly chosen individual moves to a uniformly chosen other deme) occurs with probability $m$, and otherwise a reproduction event occurs in a deme chosen with probability proportional to the square of its total fitness. The drive is released as $i \ll N$ drive homozygotes in one deme. Let $E$ be the event that the drive allele reaches frequency $10\%$ in some other deme. Let $e_{i,j}$ be the probability that the drive escapes early stochastic loss when started from $i$ drive homozygotes and $j$ drive heterozygotes, $T$ the (essentially deterministic) time until the drive is lost from the release deme once it has escaped early loss, and $P_t^{\alpha}$ the frequency of genotype $\alpha$ in the release deme at step $t$. Treating invasion attempts at different steps as independent,

$$\mathbb P(E) \approx e_{i,0}\left(1 - \prod_{t=1}^{T}\Big(1 - m\, e_{1,0}\, \mathbb E P_t^{DD} - m\, e_{0,1}\big(\mathbb E P_t^{WD} + \mathbb E P_t^{DR}\big)\Big)\right).$$

If $\phi^\alpha$ denotes the time average of $\mathbb E P_t^\alpha$ over $[0,T]$ and $m = \mathcal O(1/T)$, then

$$\mathbb P(E) \approx e_{i,0}\Big(1 - \exp\big(-mT\,[\,e_{1,0}\phi^{DD} + e_{0,1}(\phi^{WD} + \phi^{DR})\,]\big)\Big),$$

which is of order $1$. Thus a drive that is self-limiting in a single deme still escapes with substantial probability once the expected number of migrants during its lifetime is of order one.

## Depends on

- [Moran model of a homing gene drive with resistance alleles](moran-model-of-a-homing-gene-drive-with-resistance.md)

## Expansion

Condition on the release surviving early fluctuations (probability $e_{i,0}$); otherwise the drive is lost while rare and essentially never migrates. Given survival the drive trajectory in the release deme is close to the deterministic one, so at each step a migrant carries a drive allele with probability given by the genotype frequencies, and a migrant $DD$ (respectively a heterozygote carrying $D$) founds a successful invasion with probability $e_{1,0}$ (respectively $e_{0,1}$); once established in a new deme it reaches $10\%$ with probability tending to one. Multiplying the per-step non-invasion probabilities gives the product formula; Noble et al. replace expectations by the solution of the deterministic ODE model, approximate the product by an exponential of an integral, and obtain the order-one conclusion by the time-average substitution. The choice of $10\%$ is immaterial for large $N$ as long as it is below the deterministic peak drive frequency.

## Sources

- C. Noble, B. Adlam, G. M. Church, K. M. Esvelt, M. A. Nowak, "Current CRISPR gene drive systems are likely to be highly invasive in wild populations", eLife 7 (2018), e33423, <https://doi.org/10.7554/eLife.33423> (PMC6014726), Materials and methods, "Analytic formulae for the escape probability in structured populations".
