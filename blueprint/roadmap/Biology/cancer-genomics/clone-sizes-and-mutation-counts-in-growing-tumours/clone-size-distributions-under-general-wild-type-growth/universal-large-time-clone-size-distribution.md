# Universal large-time clone size distribution under general wild-type growth

**Model.** A wild-type population grows deterministically with size $n_\tau$ at time $\tau$, where $n_\tau=0$ for $\tau<0$, $n_\tau$ is positive, continuous and increasing for $\tau>0$, and $\lim_{t\to\infty}n_{t-x}/n_t$ exists in $(0,\infty)$ for each $x\ge0$. Mutant clones are initiated as a Poisson process with rate $\mu\,n_\tau$, so the number of clones by time $t$ is $K_t\sim\mathrm{Poisson}(\mu a_t)$ with $a_t=\int_0^t n_\tau\,d\tau$. Each clone evolves as a birth-death branching process with birth rate $1$ and death rate $\beta\in[0,1)$, i.e. mutant fitness $\lambda=1-\beta>0$. Let $Y_t$ be the size of a clone sampled uniformly from the initiated clones, and let

$$\delta^*=\lim_{t\to\infty}\frac{\log n_t}{t}\ge0, \qquad \gamma^*=\frac{\delta^*}{\lambda}.$$

(The growth assumption forces $n_{t-x}/n_t\to e^{-\delta^* x}$.) Growth is *exponential-type* if $\delta^*>0$ and *subexponential* if $\delta^*=0$.

**Theorem (universal limit).** With $\xi=(\beta-s)/(1-s)$, for $|s|<1$,

$$\lim_{t\to\infty}\frac{a_t}{n_t}\Bigl(\mathbb{E}\bigl[s^{Y_t}\bigr]-\beta\Bigr) = -\sum_{k\ge1}\frac{\xi^k}{\gamma^*+k}.$$

Consequently, as $t\to\infty$:

- for exponential-type growth ($\gamma^*>0$) the clone size has a proper two-parameter limit law, with

$$\mathbb{P}(Y_t=k)\to\frac{\delta^*\,\Gamma(k)}{(\gamma^*+1)_k}\;{}_2F_1\bigl(k,\gamma^*;1+\gamma^*+k;\beta\bigr), \qquad k\ge1,$$

whose tail decays as a power law $k^{-1-\gamma^*}$;

- for subexponential growth ($\gamma^*=0$), $\mathbb{P}(Y_t=k)\sim\dfrac{n_t}{a_t\,k}$ for each fixed $k\ge1$, a $1/k$ tail with total mass escaping to infinity.

**Mean and variance.** As $t\to\infty$, $\mathbb{E}[Y_t]\to\delta^*/(\delta^*-\lambda)$ if $\lambda<\delta^*$, while $\mathbb{E}[Y_t]$ grows subexponentially if $\delta^*=\lambda$ and like $e^{(\lambda-\delta^*)t}$ times a subexponential factor if $\delta^*<\lambda$; the variance is bounded iff $\delta^*>2\lambda$, with the same three-regime structure at $\delta^*=2\lambda$.

The total mutant count $B_t=\sum_{i\le K_t}Y_t^{(i)}$ is compound Poisson, and when $\mathbb{E}K_t\to0$ the law of $B_t$ given $B_t>0$ matches that of $Y_t$ given $Y_t>0$ up to $O(\mathbb{E}K_t)$. The classical Luria-Delbrück (Lea-Coulson) law is the special case $n_\tau=e^{\delta\tau}$.

## Expansion

1. A clone initiated at time $T$ has the geometric-type law of a birth-death process run for $t-T$, and $T$ has density $n_\tau/a_t$ on $[0,t]$; averaging the birth-death generating function $1-\lambda/(1-\xi e^{-\lambda(t-\tau)})$ over $T$ gives an exact integral formula.
2. Regular variation theory (Karamata's characterization) turns the growth assumption into $n_{t-x}/n_t\to e^{-\delta^* x}$, so late-time contributions are weighted by $e^{-\delta^* x}$ in the age $x=t-T$.
3. Expanding in $\xi$ and integrating $\int_0^\infty e^{-\delta^* x}e^{-k\lambda x}\,dx=1/(\lambda(\gamma^*+k))$ term by term gives the series; reading coefficients yields the hypergeometric form and the power-law tail.

## Sources

- M. D. Nicholson, T. Antal, *Universal asymptotic clone size distribution for general population growth*, arXiv:1604.04936 (Section 2 model; Section 3 mapping to total mutant number; Section 5.2 mean and variance; Section 5.3 large-time generating-function theorem and its corollary). <https://doi.org/10.48550/arXiv.1604.04936> Published version: Bulletin of Mathematical Biology 78 (2016) 2243–2276, <https://doi.org/10.1007/s11538-016-0221-x>.
