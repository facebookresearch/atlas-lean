# Tilted measures

For measures $\mu_n$ on a measurable space $X$, a function $F : X \to \mathbb{R}$ and
$n \in \mathbb{N}$, the tilted measure is

$$Q_n = \Big(\int e^{nF} \, d\mu_n\Big)^{-1} e^{nF} \mu_n ,$$

the measure $\mu_n$ reweighted by the density $e^{nF}$ and renormalised (the normalising integral
taken in $[0, \infty]$, with $0^{-1} = \infty$ and $\infty^{-1} = 0$). It is a probability measure
when the normalising integral $Z_n = \int e^{nF} \, d\mu_n$ is positive and finite, for example for a
probability measure $\mu_n$ and a bounded $F$. Otherwise it is the zero measure: for $Z_n = \infty$
because $\infty^{-1} = 0$, and for $Z_n = 0$ because the reweighted measure $e^{nF} \mu_n$ is then
zero.
