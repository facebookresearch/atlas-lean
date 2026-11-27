# Neutral divergence dating and the missing-divergence estimator of the yearly mutation rate

**Neutral dating.** Let two present-day genomes have mean time $t$ (in years) to their common ancestor at neutral sites, and let each lineage accumulate substitutions at yearly rate $\mu_y$ per base pair. Under the infinite-sites approximation the expected sequence divergence is

$$\mathbb E\, d = 2\mu_y t,$$

so a rate gives a date, $\hat t = d/(2\mu_y)$, and a date gives a rate, $\hat\mu_y = d/(2\hat t)$. For closely related species $t$ exceeds the species split time by the mean coalescence time in the ancestral population, so a rate obtained from a fossil split time is biased upward unless that excess is accounted for.

**Missing-divergence estimator.** Let $M$ be a present-day genome, $A$ an ancient genome directly dated to $T_a$ years before present, and $O$ an outgroup. Assume that the lineages of $A$ and $M$ coalesce with each other before either coalesces with the lineage of $O$, at time $\tau$ before present, and that substitutions accrue on every lineage at a possibly time-varying yearly rate $\mu_y(s)$, $s$ years before present, the same on all lineages at a given time. Then

$$\mathbb E\, d(M, O) - \mathbb E\, d(A, O) = \int_0^{T_a} \mu_y(s)\, ds,$$

so

$$\hat{\bar\mu}_y = \frac{d(M, O) - d(A, O)}{T_a}$$

estimates the average yearly mutation rate over the last $T_a$ years, with no reference to generation times, pedigrees or fossil calibrations.

## Depends on

- [Yearly mutation rate under sex-specific generation times](yearly-mutation-rate-under-sex-specific-generation-times.md)
- [Infinite-sites mutation on a finite genealogy](../../../coalescent-theory/poisson-mutation-on-the-kingman-genealogy/branch-mutation-kernel.md)

## Expansion

The two lineages joining $M$ and $O$ each run from the present back to $\tau$, giving $\mathbb E\, d(M, O) = 2\int_0^\tau \mu_y(s)\,ds$. The lineage of $A$ stops accumulating substitutions at its death, $T_a$ years ago, so $\mathbb E\, d(A, O) = \int_{T_a}^\tau \mu_y(s)\,ds + \int_0^\tau \mu_y(s)\,ds$. Subtracting cancels everything except the stretch of the modern lineage that the ancient genome never lived through, the "missing" divergence. With a constant rate this is $\mu_y T_a$ and the neutral dating identity follows as the special case of two present-day lineages. Postmortem damage and sequencing error in the ancient genome add spurious differences to $d(A, O)$ and bias the estimate downward, so they must be filtered. Several ancient genomes at different ages give rates averaged over different windows, in the same way that serially sampled virus genomes calibrate a tip-dated clock, and so can expose a rate that changed over time, as the generation-time dependence of the yearly rate predicts.

## Sources

- P. Moorjani, Z. Gao, M. Przeworski, *Human germline mutation and the erratic evolutionary clock*, PLoS Biology 14 (2016), e2000744, <https://doi.org/10.1371/journal.pbio.2000744>, PMCID PMC5070741. Section "The Puzzle" (expected divergence $d = 2\mu t$, the estimates $t = d/2\mu$ and $\mu_y = d/2\hat t$, divergence versus split time) and section "Next Steps" (the missing sequence divergence between a dated ancient genome and an outgroup as an estimate of the average yearly rate, and the analogy with tip calibration). The integral identity is derived here from the stated assumptions.
