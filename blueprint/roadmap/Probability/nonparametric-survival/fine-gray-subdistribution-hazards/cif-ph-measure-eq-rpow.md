# Baseline form of the cumulative incidence in the explicit family

Consider the family in which, given covariates $x$, a latent $\omega \sim \mathrm{Exp}(e^{\langle\beta, x\rangle})$ gives failure time $\omega/(1 - \omega)$ from the cause of interest if $\omega < 1$ and time $1$ from a competing cause otherwise. For $t \ge 0$, $F_c(t; x) = 1 - (1 - F_c(t; 0))^{e^{\langle\beta, x\rangle}}$.
