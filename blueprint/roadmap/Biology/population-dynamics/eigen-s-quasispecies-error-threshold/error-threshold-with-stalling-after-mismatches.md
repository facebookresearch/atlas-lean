# Error threshold with stalling after mismatches

**Classical threshold.** In Eigen's single-peak replication model a master sequence $X$ of relative replication rate $r > 1$ is copied without error with probability $q = (1-\mu)^L$, where $\mu \in (0,1)$ is the per-site error rate and $L$ the number of informative sites; every erroneous copy is a mutant $Y$ of relative rate $1$. Under constant resources and conserved total density, the master sequence persists at a positive stationary density if and only if $L < L^* = (\ln r)/\mu$ (to first order in $\mu$, using $\ln(1-\mu) \approx -\mu$), often quoted as $L^* \approx 1/\mu$ at $r = e$.

**Stalling model.** Suppose instead that a misincorporation during copying produces an incomplete strand $Z$ whose further extension is slower than extension from a matched terminus by a stalling factor $S \ge 0$ (the ratio of matched to mismatched extension rates), so that a copy containing errors is completed later than an accurate copy; mutants undergo the analogous reactions, strand separation is fast relative to chemical copying, resources are constant and $[X] + [Y] + [Z]$ is conserved. In the deterministic large-population limit the master sequence has a positive stationary density exactly when

$$L < L_S^* = \frac{\ln\bigl(r + \mu S (r-1)\bigr)}{\mu}.$$

**Properties.** For $r > 1$, $L_S^* \ge L^*$ for every $S \ge 0$, with equality exactly at $S = 0$; $L_S^*$ is strictly increasing in $S$ and in $r$ and still scales as $1/\mu$. The gain enters through $\mu S$ because strands carrying several errors are stalled several times.

## Depends on

- [Error threshold](master-equilibrium-pos-iff.md)
- [Maximal genome length](one-lt-mul-pow-iff.md)

## Expansion

Accurate copies of the master finish quickly and start the next round of replication, while inaccurate copies wait in the stalled state, so stalling lowers the effective production rate of mutants relative to masters and acts like an increase of the master's relative fitness from $r$ to $r + \mu S(r-1)$ inside the logarithm. With nonenzymatic template-directed polymerization measured at $\mu \approx 0.076$ and $S \approx 124$, the classical bound gives $L^* \approx 13$ informative sites at $r = e$, whereas the stalling bound gives $L_S^* \approx 39$, long enough for short functional nucleic acids. A variant in which slowly completed copies are more likely to be degraded gives the same threshold.

## Sources

- S. Rajamani, J. K. Ichida, T. Antal, D. A. Treco, K. Leu, M. A. Nowak, J. W. Szostak, I. A. Chen, "Effect of stalling after mismatches on the error catastrophe in nonenzymatic nucleic acid replication", Journal of the American Chemical Society (2010), Introduction and Results ("Modified Error Threshold Including the Effect of Stalling after Mutation"), <https://doi.org/10.1021/ja100780p> (PMC2857888).
