# Interval incidence intensity is nonnegative on an ordered window

Let $a \le b$ be real numbers (an observation window), $\rho$ a reporting fraction with
$0 \le \rho \le 1$, $\beta \ge 0$ a transmission rate, $N > 0$ a population size, $c \ge 0$ a
background rate, and $S, I : \mathbb{R} \to \mathbb{R}$ continuous functions with $S(t) \ge 0$ and
$I(t) \ge 0$ for every $t$ (susceptible and infected numbers). Then the interval intensity

$$\rho \int_a^b \frac{\beta\, S(t)\, I(t)}{N}\, dt + c\,(b - a)$$

is nonnegative, so it can serve as the mean of a Poisson count of reports over the window: a
fraction $\rho$ of the incidence $\beta S I / N$ integrated over the window plus background reports
at rate $c$. The incidence integrates new infections; the prevalence $I(t)$ is not interval
incidence.
