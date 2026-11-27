# Large-time drug concentration under random nonadherence

**Model.** In a one-compartment model with first-order absorption (rate $k_a$) and elimination (rate $k_e\neq k_a$), a dose $D$ with bioavailability $F$ is prescribed every $\tau$ time units. Let $\xi_n\in\{0,1\}$ record whether the patient remembers the $n$th dose; $(\xi_n)$ is a stationary, ergodic and possibly correlated sequence. A *dosing protocol* takes amount $Df_n$, with $f_n=f(\xi_{n-m},\dots,\xi_n)$, $f_n=0$ when $\xi_n=0$. The concentration is

$$c(t)=\kappa\sum_{n=0}^{\lfloor t/\tau\rfloor}\Big(e^{-k_e(t-n\tau)}-e^{-k_a(t-n\tau)}\Big)f_n,\qquad \kappa=\frac{DF}{V}\frac{k_a}{k_a-k_e}.$$

Write $\alpha=e^{-k_e\tau}$ and $\beta=e^{-k_a\tau}$. Two protocols are compared: *single dose*, where $f_n=\xi_n$; and *double dose*, where $f_n=0$ if $\xi_n=0$, $f_n=1$ if $\xi_n=\xi_{n-1}=1$, and $f_n=2$ if $\xi_n=1,\ \xi_{n-1}=0$.

**Theorem.**

1. For each $t\in[0,\tau]$, $c(N\tau+t)\Rightarrow C(t)=\kappa\big(\alpha^{t/\tau}A-\beta^{t/\tau}B\big)$ as $N\to\infty$, where $A$ and $B$ are equal in law to the perpetuities $\sum_{n\ge0}\alpha^nf_{-n}$ and $\sum_{n\ge0}\beta^nf_{-n}$ of the two-sided stationary dose sequence. Time averages of $c^j$ converge almost surely to the corresponding moments of $C$.
2. $\mathbb E[A]=\frac1{1-\alpha}\sum_xf(x)\pi(x)$ and $\mathbb E[B]=\frac1{1-\beta}\sum_xf(x)\pi(x)$, where $\pi$ is the stationary law of the history window. Second moments are given by explicit finite sums.
3. For i.i.d. adherence with $\mathbb P(\xi_n=1)=p$, the relative mean concentration is $\mu^{\mathrm{single}}=p<\mu^{\mathrm{double}}=p+p(1-p)$. The relative root-mean-square error decomposes as $\varepsilon=\sqrt{(\varepsilon^{\mathrm{perf}})^2+\eta}$, where $\eta\ge0$ is an explicit quadratic polynomial in $1-p$.
4. *(Toxicity.)* Under the single-dose protocol, the largest possible concentration over all adherence patterns equals that of perfect adherence, attained at $t^*=\tau\ln\!\big(\frac{(1-\alpha)\ln\beta}{(1-\beta)\ln\alpha}\big)/\ln(\alpha/\beta)$, so missed doses never raise the peak. The double-dose protocol obeys an explicit higher upper bound.

## Proof sketch

The concentration at a fixed phase of the dosing cycle is a linear filter of the dose sequence with geometric weights $\alpha^n$ and $\beta^n$, which gives a perpetuity-type limit $C$. Because the filter is linear, means depend only on the long-run fraction of dose taken, and second moments depend on the two-point correlations of $f_n$. These are explicit for finite-memory protocols. Comparing $\mu,\varepsilon$ and the overshoot $\theta$ across protocols and drug parameters gives a quantitative way to design regimens that are forgiving to nonadherence. For example, a double-dose catch-up rule raises the mean exposure. Whether it also reduces the fluctuation error $\varepsilon$, and at what toxicity cost $\theta$, depends on $k_a\tau$, $k_e\tau$ and $p$.

## Sources

- Elijah D. Counterman and Sean D. Lawley, "Designing Drug Regimens that Mitigate Nonadherence", *Bulletin of Mathematical Biology* 84 (2022), 20, <https://doi.org/10.1007/s11538-021-00976-3>. Preprint version: arXiv:2108.08358 (2021), Section 2 (model and statistics $\mu,\varepsilon,\theta$), Theorem 1 (large-time limit), Theorem 2 (moments), Corollaries 3–4 (single and double dose protocols), Theorem 5 (maximum concentration), <https://doi.org/10.48550/arXiv.2108.08358>.
