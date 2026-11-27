# Survival probability of an advantageous mutant in the spatial death-birth Moran model

**Model ($\mathrm{DB}^{\mathrm f}$).** Every site of $\mathbb Z^d$ holds a type-0 (resident) or type-1 (mutant) cell. Each cell dies at rate $1$; the vacated site is refilled by an offspring of one of its $2d$ neighbours, chosen with probability proportional to fitness, residents having fitness $1$ and mutants $\lambda = 1 + \beta$ with $\beta > 0$. Thus a type-0 site with $i$ type-0 and $j$ type-1 neighbours becomes type 1 at rate $j\lambda/(i + j\lambda)$, and a type-1 site becomes type 0 at rate $i/(i + j\lambda)$. Start from a single mutant at the origin and let $\tau_\varnothing$ be the extinction time of the mutants. For comparison, in the biased voter model (birth-death updating with fitness acting on birth) the mutant set size is a random walk with drift $(\lambda-1)/(\lambda+1)$, so $\mathbb P(\text{survival}) = \beta/(1+\beta)$ in every dimension.

**One dimension.** On $\mathbb Z$ the mutant set stays an interval, its size performs a random walk with up-probability $2\lambda/(1+3\lambda)$ from size $1$ and $\lambda/(1+\lambda)$ from larger sizes, and

$$\mathbb P(\tau_\varnothing = \infty) = \frac{2(\lambda - 1)}{3\lambda - 1} = \frac{2\beta}{2 + 3\beta},$$

which is $\sim \beta$ as $\beta \to 0$ and tends to $2/3$ as $\beta \to \infty$. More generally, from a mutant interval $A$, $\mathbb P(\tau^A_\varnothing < \infty) = \frac{\lambda+1}{3\lambda-1}\,\lambda^{-(|A|-1)}$.

**Upper bound ($d \ge 2$).** With $p_1 = 2d\lambda/\bigl((2d-1) + (2d+1)\lambda\bigr)$ the probability that a lone mutant reproduces before dying,

$$\mathbb P(\tau_\varnothing = \infty) \le \left(1 + \frac{\bigl((2d-1) + \lambda\bigr)\bigl(1 + (2d-1)\lambda\bigr)}{2d(2d-1)(\lambda^2 - 1)}\right)^{-1} =: \overline\pi_1,$$

with $\overline\pi_1 \sim (2 - 1/d)\,\beta$ as $\beta \to 0$ and $\overline\pi_1 \to 2d/(2d+1)$ as $\beta \to \infty$.

**Lower bound ($d \ge 2$).** Let $I(d) = \int_0^\infty e^{-x^{(d-1)/d}}\,dx$, $q_1 = 1 - p_1$, $C_1 = (\lambda - 1)/\bigl(2d(1 + (2d-1)\lambda)\bigr)$ and $C_2 = 2C_1/(2d+1)$. Then

$$\mathbb P(\tau_\varnothing = \infty) \ge \Bigl(\frac{1}{p_1} + \frac{q_1}{p_1}\, I(d)\, C_2^{-d/(d-1)}\Bigr)^{-1} > 0,$$

so an advantageous mutant survives with positive probability for every $\beta > 0$; this lower bound is of order $\beta^{d/(d-1)}$ as $\beta \to 0$.

## Proof sketch

The key difference from the biased voter model is that an edge between a mutant $v$ with $k$ resident neighbours and a resident $w$ with $m$ mutant neighbours is biased toward $v$ by $\lambda/((2d-m) + m\lambda) - 1/(k + (2d-k)\lambda) \ge 0$, which vanishes when $k = m = 2d$ (an isolated resident surrounded by mutants next to an isolated mutant) and is maximal for $k = m = 1$. Replacing every edge by the maximal bias gives a dominating Markov random walk for the size of the mutant set, whose gambler's-ruin survival probability is $\overline\pi_1$. For the lower bound only edges to the unbounded resident component are counted: each has bias at least $C_1$, and the isoperimetric inequality $|\partial^\infty A| \ge 2|A|^{1-1/d}$ on $\mathbb Z^d$ yields a dominated walk with drift of order $k^{-1/d}$ at size $k$, whose survival probability is computed by the generalized gambler's ruin formula and bounded by the integral $I(d)$. In one dimension no zero-bias edges arise, which makes the computation exact.

## Sources

- Jasmine Foo, Einar Bjarki Gunnarsson, Kevin Leder and David Sivakoff, "Dynamics of Advantageous Mutant Spread in Spatial Death-Birth and Birth-Death Moran Models", *Communications on Applied Mathematics and Computation* 6 (2024), 576–604, <https://doi.org/10.1007/s42967-023-00278-6>. Preprint version: arXiv:2209.11852 (2022), Sections 2.4, 3 and 4.3, Proposition 6.1, Lemma 6.2, Proposition 6.3 and Corollary 6.4, <https://doi.org/10.48550/arXiv.2209.11852>.
