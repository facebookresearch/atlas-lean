# Invasion conditions for worker-sterility alleles

In the [colony dynamics model](colony-dynamics-model-for-worker-sterility-alleles.md) with queens mating $n$ times, consider a resident population fixed for $A$ (all colonies $AA,0$) and introduce the sterility allele $a$ at low frequency. Write $r_z$ for the colony reproductive rate and $p_z$ for the queen's share of males when a fraction $z$ of workers is sterile.

**Theorem (recessive allele).** The recessive sterility allele increases in frequency when rare if

$$\frac{r_{1/(2n)}}{r_0} > \frac{2(2n-1)(2 + n + n p_0)}{2n^2\big(2 + p_0 + p_{1/(2n)}\big) + n\big(3 + 3p_0 - 2p_{1/(2n)}\big) - 2(1 + p_0)} .$$

For single and double mating this reads

$$n = 1:\quad \frac{r_{1/2}}{r_0} > \frac{6 + 2p_0}{5 + 3p_0}, \qquad n = 2:\quad \frac{r_{1/4}}{r_0} > \frac{6 + 3p_0}{5 + 3p_0 + p_{1/4}} .$$

**Theorem (dominant allele).** The dominant sterility allele increases in frequency when rare if

$$\frac{r_{1/2}}{r_0}\Big(1 + p_{1/2}\, \frac{r_{1/n}}{r_0}\Big) > 2 .$$

In particular, sterility cannot invade unless sterile workers raise colony efficiency by a finite amount (for $p_0 = 0$ the single-mating threshold is $6/5$), and there are open parameter regions where it invades under double but not single mating, e.g. $p_0 = 0.8$, $p_{1/4} = 0.9$, $r_0 = 1$ give thresholds $r_{1/2} > 1.027$ for $n = 1$ but only $r_{1/4} > 1.012$ for $n = 2$.

## Depends on

- [Colony dynamics model for worker-sterility alleles](colony-dynamics-model-for-worker-sterility-alleles.md)

## Proof depends on

- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)
- [Real 2 × 2 matrices: an eigenvalue with Re > 0 iff tr > 0 or det < 0](../../../pattern-formation/turing-patterns-and-diffusion-driven-instability/exists-eigenvalue-re-pos-iff.md)

## Expansion

Only colony types reachable at low order in the mutant frequency $\epsilon$ matter. For a dominant allele these are $AA,1$ (sterile fraction $1/n$) and $Aa,0$ (sterile fraction $1/2$); linearizing gives, after dividing by $r_0^{n+1}$ and writing $a = r_{1/2}/r_0$, $b = r_{1/n}/r_0$, the matrix $\begin{pmatrix} -1 & n p_{1/2} a/2 \\ b/n & a/2 - 1\end{pmatrix}$ for $(\delta_{AA,1}, \delta_{Aa,0})$, whose dominant eigenvalue is positive exactly when its determinant $1 - \tfrac{a}{2}(1 + p_{1/2} b)$ is negative. A recessive allele is invisible at first order (heterozygous workers still reproduce), so the colony variables are expanded to order $\epsilon^2$; the decisive colony type is $Aa,1$, in which a fraction $1/(2n)$ of workers is $aa$. The $n = 1, 2$ formulas are the specializations of the general expression.

## Sources

- J. W. Olejarz, B. Allen, C. Veller and M. A. Nowak, "The evolution of non-reproductive workers in insect colonies with haplodiploid genetics", eLife 4 (2015), e08918, Results, Eqs. (1)–(2), and Materials and methods (invasion of a dominant allele, Eqs. (16)–(20); invasion of a recessive allele, Eqs. (21)–(34)), <https://doi.org/10.7554/eLife.08918>, PMCID PMC4755779.
