# Inequalities among household reproduction numbers

In the households SIR/SEIR model the population is partitioned into households (largest size $n_H \ge 2$; a randomly infected individual lies in a household of size $n$ with size-biased probability $\pi_n$). Each infective makes on average $\mu_G > 0$ **global** contacts with uniformly chosen individuals, and **local** contacts inside its household. In a single-household epidemic started by one case, let $\mu_k$ be the mean number of cases in rank generation $k$ (averaged over $\pi_n$; $\mu_0 = 1$) and $\mu_H = \sum_{k\ge1}\mu_k > 0$ the mean number of secondary household cases. The competing reproduction numbers are:

- the **basic reproduction number** $R_0$: the unique positive root of $g_0(\lambda) = 1 - \mu_G\sum_{k=0}^{n_H-1}\mu_k\,\lambda^{-(k+1)}$ (the asymptotic per-generation growth factor of infected individuals);
- the **household reproduction number** $R_* = \mu_G(1 + \mu_H)$ (households infected per infected household);
- $R_I$: the dominant eigenvalue of $\begin{pmatrix}\mu_G & \mu_H\\ \mu_G & 0\end{pmatrix}$ (all household cases attributed to the primary case), the positive root of $1 - \mu_G/\lambda - \mu_H\mu_G/\lambda^2$;
- $R_{HI}$: the root in $(a,\infty)$, $a = \max_n a^{(n)}$, of $1 - \mu_G\sum_n \pi_n/(\lambda - a^{(n)})$, with $a^{(n)} = \mu_H^{(n)}/(1 + \mu_H^{(n)})$ (equal to $\mu_G + \mu_H/(1+\mu_H)$ when all households have one size);
- $R_2$: the root in $(b,\infty)$, $b = \max_n b^{(n)}$, of $1 - \frac{\mu_G}{\lambda}\big(1 + \sum_{n\ge2}\pi_n\mu_1^{(n)}/(\lambda - b^{(n)})\big)$, with $b^{(n)} = 1 - \mu_1^{(n)}/\mu_H^{(n)}$ (geometric within-household generations with the correct mean size);
- $R_V = 1/(1 - p_C)$, where $p_C$ is the fraction of individuals that a perfect vaccine given at random must cover to bring $R_*$ to $1$ ($R_V = 1$ if $R_* \le 1$).

**Theorem (households model).**

(a) $R_* = 1 \iff R_I = 1 \iff R_0 = 1 \iff R_2 = 1 \iff R_{HI} = 1$, and these imply $R_V = 1$.

(b) In a growing epidemic ($R_0 > 1$),

$$R_* > R_I \ge R_V \ge R_0 > R_{HI} > 1 \qquad\text{and}\qquad R_I \ge R_2 > R_{HI} > 1,$$

while in a declining epidemic ($R_0 < 1$),

$$R_* < R_I \le R_0 < R_{HI} < 1 \qquad\text{and}\qquad R_I \le R_2 < R_{HI} < 1.$$

The inequalities $R_I \ge R_V$, $R_I \ge R_2$, $R_I \le R_0$, $R_I \le R_2$ are strict iff $n_H > 2$, and $R_V \ge R_0$ is strict iff $n_H > 3$.

**Theorem (growth-rate-based estimate).** Let $R_r = 1/\mathcal M_W(r)$, where $r$ is the real-time growth rate of the households model and $\mathcal M_W(\theta) = \mathbb E[e^{-\theta W}]$ for the individual generation time $W$ (the value of $R_0$ one would infer from $r$ ignoring household structure). Then $R_r = 1 \iff R_0 = 1$ for every infectivity profile; if the infectivity profile is $J\,w(t)$ with $J$ a nonnegative random variable, $R_r \ge R_0 > 1$ in a growing and $R_r \le R_0 < 1$ in a declining epidemic.

**Households–workplaces model.** With $R_*$ the clump reproduction number and $R_H$ the household–household number, $R_* > R_H > R_I \ge R_V \ge R_0 > 1$ in a growing epidemic (reversed, without $R_V$, in a declining one), with strictness iff $\max(n_H, n_W) > 2$ (resp. $> 3$ for $R_V \ge R_0$), and the $R_r$ results carry over.

So the easily computed $R_*$ always overstates, and $R_{HI}$ always understates, the individual-level threshold $R_0$; vaccinating a fraction $1 - 1/R_0$ of individuals is never enough when $n_H > 3$.

## Expansion

All the individual-based numbers are positive roots of functions $g(\lambda) = 1 - \mu_G\sum_k c_k\lambda^{-(k+1)}$ that differ only in the assumed mean within-household generation sizes $c_k$: the true $\mu_k$ for $R_0$; all secondary household cases in generation $1$ for $R_I$; geometric sequences for $R_{HI}$ and $R_2$. Each choice preserves the mean household outbreak size, so every such $g$ equals $1 - R_*$ at $\lambda = 1$; this gives the common threshold. Away from $1$ the roots are ordered by how early the household cases are placed: shifting mass to earlier generations raises the root when it exceeds $1$ and lowers it when it is below $1$. With at most two household members there is only one household generation, so several of the numbers coincide, which explains the strictness conditions on $n_H$. $R_V$ is computed from the effect of random vaccination on $R_*$ and compared with $R_0$ and $R_I$ through the same generation-function representation; the comparison of $R_r$ with $R_0$ uses the Lotka–Euler equation for the household infectivity profile.

## Sources

- Frank Ball, Lorenzo Pellis, Pieter Trapman, "Reproduction numbers for epidemic models with households and other social structures II: comparisons and implications for vaccination", arXiv (2014). Section 2 (model, $R_0$, $R_*$, $R_I$, $R_{HI}$, $R_2$, $R_V$, $R_r$), Section 3 (Theorems 1 and 2), Sections 4–5 (households–workplaces model, Theorem 3). <https://doi.org/10.48550/arXiv.1410.4469>. Published version: Mathematical Biosciences 274 (2016), 108–139, <https://doi.org/10.1016/j.mbs.2016.01.006>; locators above refer to the arXiv version.
