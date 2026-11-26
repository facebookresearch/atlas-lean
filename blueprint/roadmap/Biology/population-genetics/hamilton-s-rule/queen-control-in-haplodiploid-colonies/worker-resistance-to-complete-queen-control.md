# Worker resistance to complete queen control

**Setting.** Suppose a queen-control allele has fixed (see [invasion and stability of a queen-control allele](invasion-and-stability-of-a-queen-control-allele.md)) with complete control, so every colony has a fraction $p' = 1$ of queen-produced males and efficiency $r'$, while non-controlled colonies have values $p$ and $r$. A second mutation $b$ at a second locus acts in workers and restores their male production. When a fraction $z$ of a colony's workers is sterile (so a fraction $1 - z$ has the resistant, reproductive phenotype), write $p_z$ and $r_z$ for its fraction of queen-produced males and its efficiency, and assume the linear interpolation

$$p_z = p + (1 - p) z, \qquad r_z = r + (r' - r) z$$

(Olejarz, Veller and Nowak 2017, eq. (5)), so $z = 1$ recovers the fully controlled colony and $z = 0$ the uncontrolled one.

**Statement** (Conditions (6) and (7)). For a dominant resistance allele $b$ and queen mating number $n$:

1. $b$ cannot invade the queen-controlled population if

$$\frac{r'}{r} > \frac{4(1 - p) + n(3 + p) + \sqrt{\bigl[4(1 - p) + n(3 + p)\bigr]^2 + 4(1 + p)\bigl[5 + n + 3(n - 1)p\bigr]}}{2\bigl[5 + n + 3(n - 1)p\bigr]};$$

2. $b$ cannot fix if

$$\frac{r'}{r} > \frac{3 + 4n + p}{3 + p + 2n(1 + p)}.$$

Unlike the conditions for queen control itself, these depend on $n$.

## Depends on

- [Invasion and stability of a queen-control allele](invasion-and-stability-of-a-queen-control-allele.md)
- [Colony dynamics model for worker-sterility alleles](../non-reproductive-workers-in-haplodiploid-colonies/colony-dynamics-model-for-worker-sterility-alleles.md)

## Proof depends on

- [Invasion conditions for worker-sterility alleles](../non-reproductive-workers-in-haplodiploid-colonies/invasion-conditions-for-worker-sterility-alleles.md)
- [Evolutionary stability of worker-sterility alleles](../non-reproductive-workers-in-haplodiploid-colonies/evolutionary-stability-of-worker-sterility-alleles.md)

## Expansion

A resistance mutation in workers undoes queen control, so the question is equivalent to the stability and fixation of a worker-sterility allele, which was solved for general $p_z, r_z$ in earlier work on non-reproductive workers; the two displayed conditions are those general conditions evaluated at the interpolation (5). For example, with singly mated queens ($n = 1$) and no queen-produced males without control ($p = 0$) condition 2 becomes $r'/r > 7/5$: the guarantee that resistance cannot fix requires control to raise colony efficiency by more than $40\%$. Whether workers resist therefore depends on how colony efficiency and male parentage change with the fraction of resistant workers, which is how the model frames the question of whether queen control is coercive or is accepted by workers.

## Sources

- J. Olejarz, C. Veller and M. A. Nowak, "The evolution of queen control over worker reproduction in the social Hymenoptera", Ecology and Evolution 7 (2017), Section 3.2, eqs. (3)–(7), <https://doi.org/10.1002/ece3.3324>, PMCID PMC5648666.
- J. W. Olejarz, B. Allen, C. Veller and M. A. Nowak, "The evolution of non-reproductive workers in insect colonies with haplodiploid genetics", eLife 4 (2015), e08918, <https://doi.org/10.7554/eLife.08918>.
