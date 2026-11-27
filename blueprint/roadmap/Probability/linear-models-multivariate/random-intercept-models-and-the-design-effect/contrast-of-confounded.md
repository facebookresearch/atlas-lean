# What the contrast estimates under confounding

Assume perfect confounding: $\mathrm{batch}(d) = a + b\, \mathrm{cond}(d)$ for every donor $d$, for
real $a$ and $b$. Let $\mu$ be a probability measure on $\Omega$ and $U$ a noise process
$U_i : \Omega \to \mathbb{R}$, one for each cell $i = (d, c)$, each $U_i$ integrable with mean $0$.
Let $d_0$ and $d_1$ be donors with $\mathrm{cond}(d_0) = 0$ and $\mathrm{cond}(d_1) = 1$. Then for
all real $\mu_0$, $\tau$, $\beta$ and all cell slots $c_0$, $c_1$, the
[observed cell values](obs.md) satisfy, with $E$ the expectation under $\mu$,

$$E[Y_{(d_1, c_1)}] - E[Y_{(d_0, c_0)}] = \tau + b \beta:$$

the between-condition contrast estimates the condition effect plus $b$ times the batch effect.
