# Cutoff frequency of the driver site frequency spectrum

**Setting.** A two-type continuous-time Markov branching process starts from one type-0 cell. Type-0 cells divide at rate $a$ and die at rate $d$; at each division one offspring is a type-1 (driver) mutant with probability $v$, and independently each type-0 cell mutates to type 1 at rate $\mu$. Type-1 cells divide at rate $a+b$ ($b>0$) and die at rate $d$. Write $\lambda_0=a(1-v)-d-\mu>0$ and $\lambda_1=a+b-d$, so $\lambda_1>\lambda_0$, and $q_0=1-(d+\mu)/(a(1-v))$ for the survival probability of the type-0 population. Let $\Omega_0^\infty$ be the event that the type-0 population survives, $Y=\lim_{t\to\infty}e^{-\lambda_0 t}Z_0(t)$ (exponential with rate $q_0$ on survival), and $W=\lim_{t\to\infty}e^{-\lambda_1 t}Z_1(t)$. Under the infinite-sites assumption the **driver site frequency spectrum** $S_j(t)$ is the number of driver clones (descendant trees of a type-1 cell born to a type-0 parent) of size $j$ at time $t$; $\tau_n$ is the first time the total population reaches $n$.

**Theorem 1 (small-frequency law of large numbers).** With $P_j(s)$ the probability that a single type-1 cell has $j$ descendants after time $s$, for every fixed $j\ge 1$, conditionally on $\Omega_0^\infty$,

$$e^{-\lambda_0 t}S_j(t)\to(av+\mu)\,Y\int_0^\infty e^{-\lambda_0 s}P_j(s)\,ds\quad\text{a.s. and in } L^2,$$

and $n^{-\lambda_0/\lambda_1}S_j(\tau_n)\to(av+\mu)\,Y W^{-\lambda_0/\lambda_1}\int_0^\infty e^{-\lambda_0 s}P_j(s)\,ds$ almost surely. The limiting profile decays like $j^{-(1+\lambda_0/\lambda_1)}$ as $j\to\infty$.

**Theorem 2 (cutoff).** Let $j_k^-(t)=\min\{j:S_j(t)\le k\}$ and $j_k^+(t)=\max\{j:S_j(t)\ge k\}$. Almost surely on $\Omega_0^\infty$, both the $\liminf$ and the $\limsup$ as $t\to\infty$ (respectively $n\to\infty$) satisfy

$$\lim_{k\to\infty}\frac{\log j_k^\pm(t)}{t}=\frac{\lambda_0\lambda_1}{\lambda_0+\lambda_1},\qquad \lim_{k\to\infty}\frac{\log j_k^\pm(\tau_n)}{\log n}=\frac{\lambda_0}{\lambda_0+\lambda_1}.$$

**Proposition 5 (trichotomy at the cutoff).** Let $j(t)$ be non-decreasing and $\gamma=\lambda_0\lambda_1/(\lambda_0+\lambda_1)$.
1. If $j(t)\gg e^{\gamma t}$, then $S_{j(t)}(t)\to 0$ in $L^1$.
2. If $j(t)\sim C e^{\gamma t}$, then conditionally on $\Omega_0^\infty$, $S_{j(t)}(t)$ converges in distribution to a Poisson variable with random mean $YL$, where $L=\lim_t\mathbb{E}[S_{j(t)}(t)]$; its characteristic function is $q_0/(q_0-L(e^{i\theta}-1))$.
3. If $j(t)\ll e^{\gamma t}$, then $e^{-\lambda_0 t}j(t)^{1+\lambda_0/\lambda_1}S_{j(t)}(t)\to YL'$ in $L^1$, with $L'$ the corresponding limit of rescaled means.

## Expansion

About $(av+\mu)Ye^{\lambda_0 s}\,ds$ driver clones are founded in $[s,s+ds]$, and a clone of age $u$ has size of order $e^{\lambda_1 u}$. A clone of size $j$ is therefore about $\lambda_1^{-1}\log j$ old, and the expected number of such clones scales as $e^{\lambda_0 t}j^{-(1+\lambda_0/\lambda_1)}$. Setting this to order one gives $\log j=\gamma t$. Below the cutoff the count is a sum of many weakly dependent indicators and obeys a law of large numbers; at the cutoff it is a Poisson count whose rate is proportional to the random type-0 limit $Y$, so averaging over the exponential law of $Y$ gives a geometric distribution. The fixed-size statements follow from $\tau_n-\lambda_1^{-1}\log(n/W)\to 0$.

## Sources

- A. Ahmed, J. Foo, E. Gunnarsson, K. Leder, "The site frequency spectrum in an exponentially growing population with selection", arXiv preprint (2026), Theorem 1, Theorem 2 and Proposition 5 (Section 3), <https://doi.org/10.48550/arXiv.2607.16479>.
