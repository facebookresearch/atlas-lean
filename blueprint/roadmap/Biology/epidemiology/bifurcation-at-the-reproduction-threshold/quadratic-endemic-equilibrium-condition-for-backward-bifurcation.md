# Quadratic endemic-equilibrium condition for backward bifurcation

In many compartmental models with recruitment, every endemic equilibrium is determined by its equilibrium force of infection $\lambda^*>0$, and substituting the equilibrium compartments into the definition of $\lambda^*$ leaves a quadratic
$$
b_0(\lambda^*)^2+b_1\lambda^*+b_2=0,\qquad b_0>0,
$$
in which $b_2$ has the sign of $1-R_0$ (it vanishes exactly at $R_0=1$). Under these hypotheses:

1. if $R_0>1$ (so $b_2<0$), there is exactly one endemic equilibrium;
2. if $b_1<0$ and either $b_2=0$ or $b_1^2-4b_0b_2=0$, there is exactly one endemic equilibrium;
3. if $R_0<1$ (so $b_2>0$), $b_1<0$ and $b_1^2-4b_0b_2>0$, there are exactly two endemic equilibria;
4. otherwise there is none.

Case 3 means that endemic equilibria coexist with the disease-free equilibrium for some $R_0<1$, the signature of a backward bifurcation: the branch of endemic equilibria turns back at a saddle-node $R_0=R_0^c<1$, where $b_1^2=4b_0b_2$. When $b_1\ge 0$ throughout, no endemic equilibrium exists for $R_0<1$ and the bifurcation at $R_0=1$ is forward. The two COVID-19 sources, eight-compartment models with quarantine, isolation, asymptomatic carriers and an environmental viral-load class, both reach this quadratic and state the four cases.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The positive roots of a quadratic with $b_0>0$ follow from Descartes' rule of signs. If $b_2<0$ the product of the roots $b_2/b_0$ is negative, so exactly one root is positive. If $b_2>0$ both roots have the same sign as $-b_1$, so two positive roots require $b_1<0$ and a positive discriminant. With $b_2=0$ the roots are $0$ and $-b_1/b_0$, positive iff $b_1<0$. Coexistence of two endemic equilibria for $R_0<1$ is necessary but not sufficient evidence of a backward bifurcation through the disease-free state; the Castillo-Chavez–Song criterion ($a>0$) settles the local picture at $R_0=1$.

## Sources

- M. A. Khan, A. Atangana, E. Alzahrani, Fatmawati, "The dynamics of COVID-19 with quarantined and isolation", *Advances in Difference Equations* 2020 (2020) 425. <https://doi.org/10.1186/s13662-020-02882-9>. PMCID: PMC7427274. (Theorem 2.)
- M. A. Aba Oud, A. Ali, H. Alrabaiah, S. Ullah, M. A. Khan, S. Islam, "A fractional order mathematical model for COVID-19 dynamics with quarantine, isolation, and environmental viral load", *Advances in Difference Equations* 2021 (2021) 106. <https://doi.org/10.1186/s13662-021-03265-4>. PMCID: PMC7877321. (Theorem 3.)
