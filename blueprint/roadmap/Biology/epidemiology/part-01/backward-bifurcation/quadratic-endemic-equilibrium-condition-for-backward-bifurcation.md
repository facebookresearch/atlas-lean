# Quadratic endemic-equilibrium condition for backward bifurcation

In many compartmental models with recruitment, every endemic equilibrium is determined by its equilibrium force of infection $\lambda^*>0$, and substituting the equilibrium compartments into the definition of $\lambda^*$ leaves a quadratic

$$
b_0(\lambda^*)^2+b_1\lambda^*+b_2=0,\qquad b_0>0,
$$

in which $b_2$ has the sign of $1-R_0$ (it vanishes exactly at $R_0=1$), and endemic equilibria correspond one-to-one to positive roots. Under these hypotheses:

1. if $R_0>1$ (so $b_2<0$), there is exactly one endemic equilibrium;
2. if $b_1<0$ and either $b_2=0$ or $b_1^2-4b_0b_2=0$, there is exactly one endemic equilibrium;
3. if $R_0<1$ (so $b_2>0$), $b_1<0$ and $b_1^2-4b_0b_2>0$, there are exactly two endemic equilibria;
4. otherwise there is none.

Case 3 means that endemic equilibria coexist with the disease-free equilibrium for some $R_0<1$, the signature of a backward bifurcation; case 2 with $b_2>0$ is the boundary between cases 3 and 4, a single double-root equilibrium, and in the sources the critical value $R_0^c<1$ below which no endemic equilibrium exists is the value of $R_0$ at which $b_1^2=4b_0b_2$. When $b_1\ge 0$, no endemic equilibrium exists for $R_0\le 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The positive roots of a quadratic with $b_0>0$ follow from the signs of its coefficients. If $b_2<0$ the product of the roots $b_2/b_0$ is negative, so exactly one root is positive. If $b_2>0$ both roots have the same sign as $-b_1$, so positive roots require $b_1<0$ and a nonnegative discriminant: two distinct roots when it is positive, one double root when it is zero. With $b_2=0$ the roots are $0$ and $-b_1/b_0$, positive iff $b_1<0$. Coexistence of two endemic equilibria for $R_0<1$ is not by itself a statement about the local picture at $R_0=1$; the [Castillo-Chavez–Song centre-manifold bifurcation theorem](castillo-chavez-song-centre-manifold-bifurcation-theorem.md) ($a>0$, $b>0$) settles that. In models with an imperfect (leaky) vaccine, the infection of vaccinated individuals produces the negative $b_1$; the COVID-19 sources below, eight-compartment models with quarantine, isolation, asymptomatic carriers and an environmental viral-load class, and a COVID-19 vaccination model all reach this quadratic.

## Sources

- M. A. Khan, A. Atangana, E. Alzahrani, Fatmawati, "The dynamics of COVID-19 with quarantined and isolation", *Advances in Difference Equations* 2020 (2020) 425. <https://doi.org/10.1186/s13662-020-02882-9>. PMCID: PMC7427274. (Theorem 2.)
- M. A. Aba Oud, A. Ali, H. Alrabaiah, S. Ullah, M. A. Khan, S. Islam, "A fractional order mathematical model for COVID-19 dynamics with quarantine, isolation, and environmental viral load", *Advances in Difference Equations* 2021 (2021) 106. <https://doi.org/10.1186/s13662-021-03265-4>. PMCID: PMC7877321. (Theorem 3.)
- Z.-H. Shen, Y.-M. Chu, M. A. Khan, S. Muhammad, O. A. Al-Hartomy, M. Higazy, "Mathematical modeling and optimal control of the COVID-19 dynamics", Results in Physics 31 (2021) 105028, vaccination model (Theorems 3–5), <https://doi.org/10.1016/j.rinp.2021.105028>, PMCID: PMC8627298.
