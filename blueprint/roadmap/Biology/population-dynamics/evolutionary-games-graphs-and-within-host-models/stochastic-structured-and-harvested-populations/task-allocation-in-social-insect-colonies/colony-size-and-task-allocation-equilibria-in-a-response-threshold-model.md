# Colony size and task allocation equilibria in a response threshold model

**Model.** A colony of $N$ workers is divided among $m$ task groups with proportions $x_i=T_i/N$ ($\sum_ix_i=1$); task $i$ has demand $D_i$, average internal response threshold $\theta_i$, worker mortality $\mu_i$ (ordered $\mu_1\le\dots\le\mu_m$), demand growth $\gamma_i$ and demand reduction efficiency $\alpha_i$. Recruitment has an Allee-type rate $rN^{s}/(b+N^{s})$ and workers switch tasks after social contacts with a probability proportional to the relative stimulus $D_j/\theta_j$. With $\Sigma=\sum_k D_k/\theta_k$:

$$
\begin{aligned}
N'&=N\Bigl[\frac{rN^{s-1}}{b+N^s}-\sum_{j=1}^m\mu_jx_j\Bigr],\\
x_i'&=\frac{rN^{s-1}}{b+N^s}\Bigl[\frac{D_i/\theta_i}{\Sigma}-x_i\Bigr]+\frac{x_i\bigl[D_i/\theta_i-\sum_jx_jD_j/\theta_j\bigr]}{\Sigma}-\mu_ix_i+x_i\sum_{j}\mu_jx_j,\\
D_i'&=N\bigl[\gamma_i-\alpha_ix_iD_i\bigr].
\end{aligned}
$$

Let $f(N,\mu)=\mu(b+N^s)-rN^{s-1}$, $N_c(\mu)=r(s-1)/(\mu s)$, and $\hat D_i=\gamma_i/(\theta_i\alpha_i)$ (relative demand). If $s>1$ and $f(N_c(\mu_m),\mu_m)<0$, there are roots $N_1^\pm$, $N_m^\pm$ of $f(\cdot,\mu_1)$, $f(\cdot,\mu_m)$ with $N_1^-<N_m^-<N_m^+\le N_1^+$. Condition **H**: $s>1$, $f(N_c(\mu_m),\mu_m)<0$ and $N(0)>N_m^-$.

**Theorem (basic dynamics).** With positive parameters and **H**, the state space $\mathbb{R}_+\times\{x\in[0,1]^m:\sum x_i=1\}\times\mathbb{R}_+^m$ is positively invariant, solutions are bounded, and

$$
N_m^+\le\liminf_{t\to\infty}N(t)\le\limsup_{t\to\infty}N(t)\le N_1^+,\qquad \liminf_{t\to\infty}D_i(t)\ge\frac{\gamma_i}{\alpha_i};
$$

if $N(0)<N_1^-$ then $\liminf_{t\to\infty}N(t)=0$. Every equilibrium has $D_i^*=\gamma_i/(\alpha_ix_i^*)$ and $rN^{*\,s-1}/(b+N^{*\,s})=\sum_j\mu_jx_j^*$.

**Theorem (two task groups).** Let $s=m=2$, $\mu_1<\mu_2$ (task 1 inside the nest, task 2 outside) and **H**. Then there are two interior equilibria with

$$
N_\pm^*=\frac{r\pm\sqrt{r^2-4b\mu^2}}{2\mu},\qquad \mu=\mu_1x_1^*+\mu_2(1-x_1^*),
$$

where $x_1^*\in(0,1)$ is the positive root of

$$
(1-x_1)^2=\frac{\mu_1\hat D_2}{\mu_2\hat D_1}x_1^2+\frac{x_1(1-x_1)}{\mu_2}\Bigl[\Bigl(1+\frac{\hat D_2}{\hat D_1}\Bigr)x_1-1\Bigr].
$$

The equilibrium with $N_-^*$ is unstable; $N_+^*$ lies between $\frac{r+\sqrt{r^2-4b\mu_2^2}}{2\mu_2}$ and $\frac{r+\sqrt{r^2-4b\mu_1^2}}{2\mu_1}$, increases with the inside allocation $x_1^*$ and decreases with $x_2^*$, $\mu_1$ and $\hat D_2/\hat D_1$. The inside allocation exceeds an explicit threshold $\hat x_1<1/(1+\hat D_2/\hat D_1)$, increases with $\hat D_1/\hat D_2$ and with $\mu_2$, and decreases with $\mu_1$.

## Expansion

At equilibrium the demand equations fix $D_i^*$ and the colony-size equation balances recruitment against the allocation-weighted mortality $\mu$, so the colony size solves the quadratic $\mu N^2-rN+b\mu=0$ for $s=2$; the smaller root is the Allee threshold and the larger root the mature colony. A larger inside allocation lowers $\mu$ and raises $N_+^*$, which is the model's explanation for mature colonies shifting workers to safer inside tasks while small colonies invest in risky foraging. The allocation equation combines a recruitment term set by the ratio of mortalities to relative demands with a social-contact term, and monotonicity in the parameters follows by implicit differentiation of the quadratic-type equation for $x_1^*$.

## Sources

- Yun Kang, Guy Theraulaz, *Dynamical models of task organization in social insect colonies*, arXiv (2015). Section 3: Lemma 3.1 (existence of positive roots), Theorem 3.1 (basic dynamical properties), Lemma 3.2 (equilibrium), Theorem 3.2 (task allocation). <https://doi.org/10.48550/arXiv.1511.04769> Published version: Bulletin of Mathematical Biology 78 (2016) 879–915, <https://doi.org/10.1007/s11538-016-0165-1>.
