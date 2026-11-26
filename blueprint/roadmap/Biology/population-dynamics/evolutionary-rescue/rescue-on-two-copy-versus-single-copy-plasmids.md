# Rescue on two-copy versus single-copy plasmids

Use the establishment probabilities $p_{\mathrm{est}}(1)$, $p_{\mathrm{est}}(2)$ and the rescue formula of the linked articles, with wild-type rates $\lambda_0 < \mu_0$ independent of copy number and no plasmid cost. Write $\lambda_{\mathrm{het}}, \mu_{\mathrm{het}}$ for the heterozygous two-copy cell.

**Proposition.**

1. *(No dosage effect: mutant homozygotes have rates $\lambda_{\mathrm{hom}} > \mu_{\mathrm{hom}}$ for both $n = 1$ and $n = 2$, and heterozygotes are no fitter than homozygotes, $\lambda_{\mathrm{het}}/\mu_{\mathrm{het}} \le \lambda_{\mathrm{hom}}/\mu_{\mathrm{hom}}$; more generally, $p_{\mathrm{est}}(1) > p_{\mathrm{est}}(2)$ holds iff $\mu_{\mathrm{het}}/\lambda_{\mathrm{het}} > \tfrac{2}{3}\,\mu_{\mathrm{hom}}/\lambda_{\mathrm{hom}}$.)* Then $p_{\mathrm{est}}(1) > p_{\mathrm{est}}(2)$, and

$$P_{\mathrm{rescue}}(n=2) > P_{\mathrm{rescue}}(n=1) \iff \frac{\lambda_{\mathrm{het}}}{\mu_{\mathrm{het}}} > \frac{3\,\lambda_{\mathrm{hom}}/\mu_{\mathrm{hom}}}{1 + 2\,\lambda_{\mathrm{hom}}/\mu_{\mathrm{hom}}}.$$

With $\mu \equiv 1$, $\lambda_{\mathrm{hom}} = 1 + s$ and $\lambda_{\mathrm{het}} = 1 + \alpha s$ this reads $\alpha > 1/(3 + 2s)$.
2. *(Dosage effect: rates depend on the absolute number of mutant copies, $\lambda_1 > \mu_1$ for one copy and $\lambda_2 \ge \lambda_1$, $\mu_2 \le \mu_1$ for two.)* Then $p_{\mathrm{est}}(2) > p_{\mathrm{est}}(1) \iff \lambda_2/\mu_2 > (\lambda_1/\mu_1)^2$, and $P_{\mathrm{rescue}}(n=2) > P_{\mathrm{rescue}}(n=1)$ always.

## Depends on

- [Establishment of a mutation on a multicopy plasmid under random segregation](establishment-on-multicopy-plasmids-under-random-segregation.md)
- [Probability of evolutionary rescue from de novo mutations](probability-of-evolutionary-rescue-from-de-novo-mutations.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Rescue with $n = 2$ is more likely iff $2p_{\mathrm{est}}(2) > p_{\mathrm{est}}(1)$. In case 1 put $h = \mu_{\mathrm{hom}}/\lambda_{\mathrm{hom}} < 1$ and $r = \mu_{\mathrm{het}}/\lambda_{\mathrm{het}}$; squaring $\sqrt{9 - 6r + 9r^2 - 8h} > 1 - 2h + 3r$ reduces to $(1-h)(2+h) > 3r(1-h)$, i.e. $r < (2+h)/3$, which is the displayed condition. In case 2 put $r = \mu_1/\lambda_1 < 1$ and $r_2 = \mu_2/\lambda_2 \le r$: $p_{\mathrm{est}}(2) > 1 - r$ reduces to $8r^2 > 8r_2$, and $2p_{\mathrm{est}}(2) > 1 - r$ follows from $9 - 14r + 9r^2 > (1 + r)^2$, i.e. $8(1-r)^2 > 0$. Without dosage effects the doubled mutational supply wins only if heterozygotes keep at least about a third of the homozygote's Malthusian fitness; with dosage effects the second copy always helps unless it carries a cost.

## Sources

- M. Santer and H. Uecker, "Evolutionary Rescue and Drug Resistance on Multicopy Plasmids", Genetics 215 (2020), 847–868, section "Analytical solutions for one and two plasmid copies per cell", Equations 6, 7, 9 and 10, <https://doi.org/10.1534/genetics.119.303012> (PMC7337077).
