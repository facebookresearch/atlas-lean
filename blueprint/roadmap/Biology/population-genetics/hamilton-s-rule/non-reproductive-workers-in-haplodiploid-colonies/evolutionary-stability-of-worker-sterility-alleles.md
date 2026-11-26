# Evolutionary stability of worker-sterility alleles

In the [colony dynamics model](colony-dynamics-model-for-worker-sterility-alleles.md) with queens mating $n$ times, consider a resident population fixed for the sterility allele $a$ (all colonies $aa,n$, so $z = 1$) and introduce the reproductive allele $A$ at low frequency.

**Theorem (recessive allele).** The recessive sterility allele is evolutionarily stable against invasion by $A$ if

$$\Big(\frac{r_1}{r_{(n-1)/n}} - \frac{n\,(1 - p_{(n-1)/n})}{2}\Big)\Big(\frac{2 r_1}{r_{1/2}} - 1\Big) > 1 .$$

For single and double mating:

$$n = 1:\ \Big(\frac{r_1}{r_0} - \frac{1 - p_0}{2}\Big)\Big(\frac{2r_1}{r_{1/2}} - 1\Big) > 1, \qquad n = 2:\ \Big(\frac{r_1}{r_{1/2}} - (1 - p_{1/2})\Big)\Big(\frac{2r_1}{r_{1/2}} - 1\Big) > 1 .$$

**Theorem (dominant allele).** The dominant sterility allele is evolutionarily stable if

$$\frac{r_1}{r_{(2n-1)/(2n)}} > \frac{2 + 3n - n\, p_{(2n-1)/(2n)}}{2(n + 1)} .$$

Invasion and stability are logically independent: for $n = 1$ all four combinations (invades or not, stable or not) occur, e.g. $r_{1/2} = 0.6$, $r_1 = 0.9$ (with $r_0 = 1$ and any $p_0 > 0.2$) is stable although sterility cannot invade. Stability may also be easier under multiple mating: with $p_0 = 0.6$, $p_{1/2} = 0.9$, $r_0 = 1$, $r_{1/2} = 1.05$, stability needs $r_1 > 1.105$ for $n = 1$ but only $r_1 > 1.087$ for $n = 2$.

## Depends on

- [Colony dynamics model for worker-sterility alleles](colony-dynamics-model-for-worker-sterility-alleles.md)
- [Invasion conditions for worker-sterility alleles](invasion-conditions-for-worker-sterility-alleles.md)

## Proof depends on

- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Expansion

For the recessive allele the relevant rare colony types are $aa,n-1$ (an $aa$ queen with one $A$ mate, so a fraction $(n-1)/n$ of workers is sterile) and $Aa,n$ (half the workers $aa$), and a first-order expansion around the all-$aa,n$ state suffices: stability is the condition that the linearized growth rate of these types is negative. For the dominant allele every first-order mutant colony has only sterile workers ($Aa$ or $aa$), so the expansion goes to second order, where the $Aa,n-1$ colony type (only a fraction $1/(2n)$ of workers being $AA$ and reproductive) enters through $r_{(2n-1)/(2n)}$ and $p_{(2n-1)/(2n)}$. The general-$n$ formulas reduce to the displayed $n = 1, 2$ cases.

## Sources

- J. W. Olejarz, B. Allen, C. Veller and M. A. Nowak, "The evolution of non-reproductive workers in insect colonies with haplodiploid genetics", eLife 4 (2015), e08918, Results, Eqs. (3)–(4), and Materials and methods (stability of a dominant allele, Eqs. (35)–(49); stability of a recessive allele, Eqs. (50)–(53)), <https://doi.org/10.7554/eLife.08918>, PMCID PMC4755779.
