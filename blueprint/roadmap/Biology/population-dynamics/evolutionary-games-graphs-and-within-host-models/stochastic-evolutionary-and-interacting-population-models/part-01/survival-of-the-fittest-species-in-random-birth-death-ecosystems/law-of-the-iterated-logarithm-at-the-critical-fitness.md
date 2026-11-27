# Law of the iterated logarithm at the critical fitness

In the species survival model of Guiol, Machado and Schinazi, the number $X_n$ of living species performs a nearest-neighbour random walk on $\mathbb Z_+$: at each step a new species is born with probability $p > \tfrac12$, and otherwise ($q = 1 - p$) the least fit living species dies (nothing happens if none is alive). Each newborn species receives an independent uniform $[0,1]$ fitness. Fix a level $f \in (0,1)$ and let $L_n$ be the number of living species with fitness below $f$, $R_n$ the number of living species with fitness at least $f$, and $B_n$ the number of species with fitness at least $f$ born by time $n$. Then $L$ is a reflected random walk with up-probability $pf$ and down-probability $q$, positive recurrent, null recurrent or transient according as $pf <$, $=$, $> q$; the **critical fitness** is

$$f_c = \frac{q}{p}.$$

$B_n - R_n$ counts the fit species that have died by time $n$; Guiol, Machado and Schinazi showed $0 \le \limsup_n (B_n - R_n)/n^{1/2+\varepsilon} \le 2/q$ a.s. at $f = f_c$, so the fitness distribution of living species becomes uniform on $(f_c, 1)$.

**Theorem.** At $f = f_c$:

(1) Almost surely,

$$\limsup_{n\to\infty}\frac{B_n - R_n}{\sqrt{4qn\ln\ln n}} = 1.$$

(2) In distribution,

$$\frac{B_n - R_n}{\sqrt{2qn}} \Longrightarrow |N(0,1)|.$$

(3) $(L_n)$ is a recurrent Markov chain, so every species with fitness below $f_c$ eventually goes extinct almost surely.

Thus at criticality the number of fit species lost grows like a reflected Brownian motion, of exact order $\sqrt{n\ln\ln n}$, mirroring the self-organized-criticality picture of the Bak–Sneppen model with a uniform fitness law above a threshold.

## Expansion

A fit species can die only when there is no unfit species alive, i.e. when $L_n = 0$ and the walk steps down. Hence $B_n - R_n$ equals the number of downward attempts made while $L$ sits at $0$, a local time of the null-recurrent walk $L$ at zero. At $f = f_c$ the walk $L$ has zero drift away from $0$ and step variance $2q$ per unit time, so its local time at $0$ behaves like that of a reflected Brownian motion. The key estimate is a law of the iterated logarithm for the return times, $\liminf_m T_m/(m^2/(2\ln\ln m)) = 1$ a.s. for the time $T_m$ of the $m$-th return of $L$ to $0$, which inverts to the stated $\limsup$; the distributional limit is Lévy's identity $\ell_t \stackrel{d}{=} |W_t|$ for Brownian local time.

## Sources

- Iddo Ben-Ari, Anastasios Matzavinos, Alexander Roitershtein, "On a species survival model", arXiv (2010). Section 1 (description of the GMS model, processes $L$, $R$, $B$, critical value $f_c$, Theorem 1), Lemma 1 and its proof. <https://doi.org/10.48550/arXiv.1006.2585>. Published version: Electronic Communications in Probability 16 (2011), 226–233, <https://doi.org/10.1214/ecp.v16-1625>; locators above refer to the arXiv version.
