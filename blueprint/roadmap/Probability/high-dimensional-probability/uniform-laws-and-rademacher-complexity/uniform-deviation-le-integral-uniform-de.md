# Concentration of the uniform deviation

**Concentration of the uniform deviation** (Wainwright, *High-Dimensional Statistics*, 2019,
§4.2, the concentration step of the uniform law via Rademacher complexity): for a countable class
$F$ of measurable functions with $|f| \le b$ for some $b > 0$, every $n \ge 1$ and every
$\delta \ge 0$, with probability at least $1 - e^{-n \delta^2 / (2 b^2)}$ over $n$ independent
samples from a probability measure $P$,
$\|P_n - P\|_F \le \mathbb{E}\big[\|P_n - P\|_F\big] + \delta$.
