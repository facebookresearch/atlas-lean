# A same-batch donor pair identifies the condition effect

Let $\mu$ be a probability measure on $\Omega$ and $U$ a noise process
$U_i : \Omega \to \mathbb{R}$, one for each cell $i = (d, c)$, each $U_i$ integrable with mean $0$.
Let $d_0$ and $d_1$ be donors in the same batch, $\mathrm{batch}(d_0) = \mathrm{batch}(d_1)$, whose
conditions differ by one, $\mathrm{cond}(d_1) = \mathrm{cond}(d_0) + 1$. Then for all real $\mu_0$,
$\tau$, $\beta$ and all cell slots $c_0$, $c_1$, the [observed cell values](obs.md) satisfy, with
$E$ the expectation under $\mu$,

$$E[Y_{(d_1, c_1)}] - E[Y_{(d_0, c_0)}] = \tau.$$

Under perfect confounding with $b \ne 0$ no such pair exists. Such a pair is sufficient, not
necessary: for three donors with batches $(0, 1, 2)$ and conditions $(0, 1, 1)$ no two donors share
a batch, yet the donor means $m_0, m_1, m_2$ satisfy $(m_1 - m_0) - (m_2 - m_1) = \tau$.
