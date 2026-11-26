# Minimal selective concentration

**Setting.** Let $s(c)$ be the [competition selection coefficient](selection-coefficient-from-a-pairwise-competition-assay.md) of a resistant strain against an isogenic susceptible strain at antibiotic concentration $c \ge 0$, and let $\mathrm{MIC}_{\mathrm{susc}} < \mathrm{MIC}_{\mathrm{res}}$ be their minimal inhibitory concentrations. Assume:

1. resistance is costly, $s(0) = -\delta < 0$;
2. $s$ is continuous and strictly increasing on $[0, \mathrm{MIC}_{\mathrm{susc}}]$;
3. $s(\mathrm{MIC}_{\mathrm{susc}}) > 0$.

**Definition and proposition.** There is a unique $c^\ast \in (0, \mathrm{MIC}_{\mathrm{susc}})$ with $s(c^\ast) = 0$, the *minimal selective concentration* (MSC). For $0 \le c < \mathrm{MSC}$ the resistant strain declines in frequency, and for $\mathrm{MSC} < c \le \mathrm{MIC}_{\mathrm{susc}}$ it is enriched. Together with the source's experimental regime where the resistant strain also outcompetes the susceptible strain on $(\mathrm{MIC}_{\mathrm{susc}}, \mathrm{MIC}_{\mathrm{res}})$, this gives the selective window $(\mathrm{MSC}, \mathrm{MIC}_{\mathrm{res}})$, strictly containing the classical mutant selection window $(\mathrm{MIC}_{\mathrm{susc}}, \mathrm{MIC}_{\mathrm{res}})$.

If near the threshold $s(c) \approx -\delta + \beta c$ with $\beta > 0$, then $\mathrm{MSC} \approx \delta/\beta$: lowering the cost $\delta$ (for example by compensatory mutation) lowers the MSC proportionally.

## Depends on

- [Selection coefficient from a pairwise competition assay](selection-coefficient-from-a-pairwise-competition-assay.md)

## Expansion

Existence and uniqueness follow from the intermediate value theorem and strict monotonicity; the sign of $s$ decides the direction of change of the log-ratio. Experimentally the MSC is the $s = 0$ intercept of $s$ plotted against concentration. The source measures MSCs between $1/4$ and $1/230$ of $\mathrm{MIC}_{\mathrm{susc}}$ (streptomycin $1/4$, tetracycline $1/100$, ciprofloxacin $1/10$ to $1/230$), and argues that the cost $\delta$, more than the resistance level $\mathrm{MIC}_{\mathrm{res}}$, sets the MSC. For de novo resistance at mutation rate $u$ in a population of size $N$, takeover is limited by the waiting time for a surviving mutant when $uN \ll 1$ and is close to deterministic sweep time, on the order of $s^{-1}$ generations times a logarithmic factor, when $uN > 1$.

## Sources

- E. Gullberg, S. Cao, O. G. Berg, C. Ilbäck, L. Sandegren, D. Hughes and D. I. Andersson, *Selection of resistant bacteria at very low antibiotic concentrations*, PLoS Pathog. 7 (2011), e1002158. <https://doi.org/10.1371/journal.ppat.1002158> (PMCID: PMC3141051). Results; Materials and Methods, "Competition experiments".
