# Optimal feature-dependent quarantine rule via the incubation density ratio

**Setting.** A potentially exposed individual has feature vector $X$ with support $\mathcal X$ and unknown infection status $I\in\{0,1\}$. If infected, $Y>0$ is the incubation period. A *quarantine rule* $t:\mathcal X\to(0,\infty)$ quarantines an individual with features $x$ for time $t(x)$. For a tolerance $\epsilon>0$ the optimal rule solves

$$
\min_t\ \mathbb E_0\,t(X)\quad\text{subject to}\quad 1-\mathbb P_1\big(Y\le t(X)\big)\le\epsilon,
$$

where subscripts $0,1$ condition on $I=0,1$: minimize the mean quarantine of uninfected people subject to an *escape probability* (an infected person not developing symptoms before release) at most $\epsilon$. Without features this is the $(1-\epsilon)$-quantile of the incubation period.

Write $X=(C,W)$ with $C$ categorical and $W\in\mathbb R^d$; let $f_1(x),f_0(x)$ be the densities of $X$ given $I=1,0$, and $F_1(y\mid x),f_1(y\mid x)$ the distribution and density of $Y$ given $X=x$, $I=1$. Assume

1. for every $x$, $f_1(y\mid x)>0$ for all $y>0$, is continuous in $y$, and is either strictly monotone in $y$ or unimodal and strictly monotone on both sides of its mode (true for Weibull, lognormal, gamma and Erlang incubation laws);
2. $0<\inf_x\mathbb P(I=1\mid X=x)\le\sup_x\mathbb P(I=1\mid X=x)<1$ and $\inf_x\sup_yf_1(y\mid x)>0$.

Let $c^*=\inf_x\sup_y f_1(y\mid x)f_1(x)/f_0(x)>0$ and, for $0<c\le c^*$,

$$
t_c(x)=\sup\Big\{y:\ \frac{f_1(y\mid x)f_1(x)}{f_0(x)}\ge c\Big\}.
$$

**Theorem.** Under conditions 1 and 2, if $\epsilon\le1-\mathbb E_1\big[F_1(t_{c^*}(X)\mid X)\big]$, there is a unique $c_0\in(0,c^*]$ with

$$
1-\mathbb E_1\big[F_1(t_{c_0}(X)\mid X)\big]=\epsilon,
$$

and $t_{c_0}(\cdot)$ is the unique minimizer of the constrained problem.

## Expansion

The problem is a Neyman–Pearson-type allocation: extending the quarantine of individuals with features $x$ by $dt$ costs $f_0(x)\,dt$ in expected uninfected quarantine time and buys $f_1(t\mid x)f_1(x)\,dt$ of symptom-detection probability, so the optimum releases each individual when this marginal benefit-to-cost ratio, the density ratio, falls below a common threshold $c_0$ (the end of the "high density ratio period"). The shape condition makes the escape probability continuous and strictly monotone in $c$, giving a unique $c_0$. A weight $w(x)$ for heterogeneous quarantine costs is handled by replacing $f_0$ with $wf_0$. In practice $f_1(y\mid x)$, $f_1$ and $f_0$ are estimated from historical quarantine data and $c_0$ is solved from the empirical constraint; applied to COVID-19 data, quarantine lengths vary with age and with the infection rate of the country of origin.

## Sources

- Ruoyu Wang, Qihua Wang. *Determination and estimation of optimal quarantine duration for infectious diseases with application to data analysis of COVID-19* (2020), Section 2: problem (1), Conditions 1–2 and Theorem 1. <https://doi.org/10.48550/arXiv.2006.05002>
