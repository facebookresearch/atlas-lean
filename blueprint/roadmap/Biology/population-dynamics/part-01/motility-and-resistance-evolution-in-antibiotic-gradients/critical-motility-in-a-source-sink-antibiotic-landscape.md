# Critical motility in a source–sink antibiotic landscape

**Staircase model.** Bacteria carry a genotype $g \in \{1, \dots, L\}$ of increasing antibiotic
resistance and occupy spatial compartments $x \in \{1, \dots, L\}$ of increasing antibiotic
concentration. Cells die at rate $\delta$, move to a neighbouring compartment at rate $\nu$
(motility), mutate between adjacent genotypes, and divide at the density-dependent rate

$$b(x, g) = \begin{cases} r\,(1 - N_x / K), & x \le g \text{ and } N_x \le K, \\ 0, & \text{otherwise}, \end{cases}$$

where $N_x$ is the number of cells in compartment $x$ and $K$ the carrying capacity. Antibiotics
block division of susceptible genotypes $g < x$.

**Source–sink reduction.** With two compartments and the wild type able to divide only in the first
($L = 2$, resistance state $R = 1$), the mean-field dynamics of the wild-type profile is

$$\dot N_1 = r\Bigl(1 - \frac{N_1}{K}\Bigr) N_1 - (\delta + \nu) N_1 + \nu N_2, \qquad
\dot N_2 = -(\delta + \nu) N_2 + \nu N_1 .$$

Besides extinction $N_1 = N_2 = 0$, it has the fixed point

$$N_1^* = K\Bigl(1 - \frac{\delta(\delta + 2\nu)}{r(\delta + \nu)}\Bigr), \qquad
N_2^* = \frac{\nu}{\nu + \delta} N_1^* .$$

**Critical motility.** Suppose the source is viable but the landscape is a sink on average,
$\delta < r < 2\delta$. Then $N^*$ is positive and globally attracts all profiles with $N_x > 0$ for
$\nu < \nu_c$, while for $\nu > \nu_c$ extinction is globally attracting, where

$$\nu_c = \frac{\delta (r - \delta)}{2\delta - r} > 0 .$$

At $\nu = \nu_c$ the two fixed points collide and exchange stability in a transcritical bifurcation.

## Expansion

The fixed point follows by substituting $N_2 = \nu N_1/(\nu + \delta)$ into the first equation:
$r(1 - N_1/K) = (\delta + \nu) - \nu^2/(\delta + \nu) = \delta(\delta + 2\nu)/(\delta + \nu)$. Positivity
of $N_1^*$ is $r(\delta + \nu) > \delta(\delta + 2\nu)$, that is $\nu(2\delta - r) < \delta(r - \delta)$,
which for $r < 2\delta$ is $\nu < \nu_c$. The bifurcation is forced: as $\nu \to 0$ cells grow locally
in the source and survive, whereas as $\nu \to \infty$ they sample both compartments and experience
the averaged net growth rate $r/2 - \delta < 0$. This critical motility defines a "deadly motility"
regime above which the wild type cannot persist and resistance cannot evolve. Below it, motility
first accelerates adaptation (when $\nu < \delta$ cells rarely change compartments in their lifetime
and the first mutant must reach the region where wild-type competition is weak) and then slows it
(when $\nu > \delta$ the wild-type profile spreads into that region and suppresses mutant fitness).

## Sources

- V. Piskovsky, N. M. Oliveira, "Bacterial motility can govern the dynamics of antibiotic
  resistance evolution", Nature Communications 14 (2023) 5584, Eqs. (1), (2), (4)-(6),
  <https://doi.org/10.1038/s41467-023-41196-8> (PMC10495427).
