# Visit-and-return metapopulation SIR model

Partition a population into $n$ regions and let $X_{ij}$ ($X\in\{S,I,R\}$) be the number of residents of region $j$ currently present in region $i$, with $X_{ii}$ the residents at home. Residents of $j$ leave home for region $i$ at per-capita rate $l_{ij}$ and visitors return home at rate $r$. Transmission in region $i$ is frequency-dependent on everyone present there, with rate $\beta_i$. With recruitment $\nu_i$, natural death $\mu$, disease death $\delta$ and progression to the removed class $\gamma$,

$$
\begin{aligned}
\dot S_{ii}&=\nu_i-\beta_iS_{ii}\frac{\sum_j I_{ij}}{\sum_j N_{ij}}-S_{ii}\sum_j l_{ji}+r\sum_j S_{ji}-\mu S_{ii},\\
\dot S_{ij}&=-\beta_iS_{ij}\frac{\sum_j I_{ij}}{\sum_j N_{ij}}+l_{ij}S_{jj}-rS_{ij}-\mu S_{ij},\\
\dot I_{ii}&=\beta_iS_{ii}\frac{\sum_j I_{ij}}{\sum_j N_{ij}}-\gamma I_{ii}-I_{ii}\sum_j l_{ji}+r\sum_j I_{ji}-(\mu+\delta)I_{ii},\\
\dot I_{ij}&=\beta_iS_{ij}\frac{\sum_j I_{ij}}{\sum_j N_{ij}}-\gamma I_{ij}+l_{ij}I_{jj}-rI_{ij}-(\mu+\delta)I_{ij},
\end{aligned}
$$

and analogous equations for $R_{ii}$, $R_{ij}$, where $N_{ij}=S_{ij}+I_{ij}+R_{ij}$. Unlike Eulerian patch models, individuals keep their residence label, so travel is a temporary visit rather than migration.

**Reproduction number.** Linearizing the infected equations at the disease-free equilibrium gives $F=F_1\oplus\dots\oplus F_n$, where $F_i$ has every row of residents present in region $i$ equal to $\beta_iS^*_{i\cdot}/\sum_jN^*_{ij}$, and a transition matrix $V$ with diagonal entries $\kappa_{ii}+\sum_j l_{ji}$ and $\kappa_{ij}+r$ ($\kappa=\gamma+\mu+\delta$), nonpositive off-diagonal entries $-l_{ij}$, $-r$, and positive column sums $\kappa_{\cdot\cdot}$. A matrix with nonpositive off-diagonal entries and positive column sums is a nonsingular M-matrix, so $V^{-1}\ge 0$ exists and

$$
R_0=\rho\big((F_1\oplus\dots\oplus F_n)V^{-1}\big),
$$

which depends on the travel rates $l_{ij}$, $r$ as well as on the regional transmission rates. Without travel ($l_{ij}=r=0$, $\beta_i=\beta$) the model reduces to the SIR model with $R_0=\beta/(\gamma+\mu+\delta)$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

Each column of $V$ follows one infected subpopulation: outflow by removal ($\kappa$) and by travel or return, with the travel or return flow reappearing as inflow to another subpopulation. The departures cancel in the column sum, leaving $\kappa>0$, so $V$ is column diagonally dominant with a positive diagonal and therefore a nonsingular M-matrix. $FV^{-1}$ is then nonnegative and the van den Driessche–Watmough theory applies. Parameterized with census, prevalence and mobile-phone trip data for twenty regions of Kenya, the model shows that mobility moves HIV from high- to low-prevalence regions, raising incidence slightly where prevalence is low and lowering it where prevalence is high, with a small net effect nationally.

## Sources

- A. Isdory, E. W. Mureithi, D. J. T. Sumpter, "The impact of human mobility on HIV transmission in Kenya", *PLoS ONE* 10 (2015) e0142805. <https://doi.org/10.1371/journal.pone.0142805>. PMCID: PMC4657931. (Eqs. (1)–(8), Theorem 1.)
