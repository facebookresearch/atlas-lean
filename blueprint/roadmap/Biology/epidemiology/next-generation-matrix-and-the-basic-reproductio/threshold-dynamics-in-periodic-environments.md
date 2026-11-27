# Threshold dynamics of compartmental epidemic models in periodic environments

This page covers a research target from Wang and Zhao (2008). For a $T$-periodic compartmental model $x' = \mathcal{F}(t, x) - \mathcal{V}(t, x)$ with a disease-free periodic solution, the basic reproduction number $\mathcal{R}_0$ is defined as the spectral radius of the next-generation operator on $T$-periodic functions. The target is the threshold theorem:

- $\mathcal{R}_0 - 1$ has the same sign as $r(\Phi_{F - V}(T)) - 1$, with $\Phi_{F - V}$ the monodromy matrix of the linearized infected subsystem;
- the disease-free periodic solution is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.

The reproduction number of the time-averaged autonomous system can underestimate or overestimate the periodic $\mathcal{R}_0$. The autonomous case is [the threshold for the linearized infected subsystem](is-hurwitz-sub-iff-r0-lt-one.md).

## Expansion

Fix from the source the periodic analogues of the conditions on $\mathcal{F}$ and $\mathcal{V}$, state the two parts as theorems, and prove them; give an example in which the averaged reproduction number differs from the periodic one, as a separate statement.

Prerequisites:

- [Basic reproduction number of the next-generation matrix](r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](is-hurwitz-sub-iff-r0-lt-one.md)

## Sources

- W. Wang and X.-Q. Zhao, Threshold dynamics for compartmental epidemic models in periodic environments, *J. Dynam. Differential Equations* 20 (2008), 699–717, <https://doi.org/10.1007/s10884-008-9111-8>.
