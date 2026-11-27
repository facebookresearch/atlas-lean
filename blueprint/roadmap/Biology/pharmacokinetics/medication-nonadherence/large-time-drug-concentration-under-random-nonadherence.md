# Large-time drug concentration under random nonadherence

**Model.** In a one-compartment model with first-order absorption (rate $k_a$) and elimination (rate $k_e\neq k_a$), a dose $D$ with bioavailability $F$ is prescribed every $\tau$ time units. Let $\xi_n\in\{0,1\}$, $n\in\mathbb Z$, record whether the patient remembers the $n$th dose, fix $m\ge0$, and let $X_n=(\xi_{n-m},\dots,\xi_n)\in\{0,1\}^{m+1}$ be the history window. Assume $(X_n)_{n\in\mathbb Z}$ is a stationary, irreducible, time-homogeneous Markov chain on $\{0,1\}^{m+1}$ with transition matrix $P$ and stationary law $\pi$ ($P^{\top}\pi=\pi$); the $\xi_n$ may be correlated. A *dosing protocol* is a function $f:\{0,1\}^{m+1}\to[0,\infty)$, and the $n$th dose is $Df_n$ with $f_n=f(X_n)$. The concentration is

$$c(t)=\kappa\sum_{n=0}^{\lfloor t/\tau\rfloor}\Big(e^{-k_e(t-n\tau)}-e^{-k_a(t-n\tau)}\Big)f_n,\qquad \kappa=\frac{DF}{V}\frac{k_a}{k_a-k_e}.$$

Write $\alpha=e^{-k_e\tau}$ and $\beta=e^{-k_a\tau}$. Two protocols are compared: *single dose*, where $f_n=\xi_n$; and *double dose*, where $f_n=0$ if $\xi_n=0$, $f_n=1$ if $\xi_n=\xi_{n-1}=1$, and $f_n=2$ if $\xi_n=1,\ \xi_{n-1}=0$.

**Theorem.**

1. For each $t\in[0,\tau]$, $c(N\tau+t)\Rightarrow C(t)=\kappa\big(\alpha^{t/\tau}A-\beta^{t/\tau}B\big)$ as $N\to\infty$, where $A$ and $B$ are equal in law to the perpetuities $\sum_{n\ge0}\alpha^nf_{-n}$ and $\sum_{n\ge0}\beta^nf_{-n}$ of the two-sided stationary dose sequence. Time averages of $c^j$ converge almost surely to the corresponding moments of $C$.
2. $\mathbb E[A]=\frac1{1-\alpha}\sum_xf(x)\pi(x)$ and $\mathbb E[B]=\frac1{1-\beta}\sum_xf(x)\pi(x)$, sums over $x\in\{0,1\}^{m+1}$. For the second moments let $v(x)=f(x)\pi(x)$ and $u_\gamma=(I-\gamma P^{\top})^{-1}v$ for $\gamma\in\{\alpha,\beta\}$. Then

$$\mathbb E[AB]=\frac1{1-\alpha\beta}\Big(\sum_xf(x)\big(u_\alpha(x)+u_\beta(x)\big)-\sum_xf(x)^2\pi(x)\Big),$$

$\mathbb E[A^2]$ and $\mathbb E[B^2]$ are the same expression with $\beta$ replaced by $\alpha$, respectively $\alpha$ by $\beta$, and $\mathbb E[C(t)^2]=\kappa^2\big(\alpha^{2t/\tau}\mathbb E[A^2]-2\alpha^{t/\tau}\beta^{t/\tau}\mathbb E[AB]+\beta^{2t/\tau}\mathbb E[B^2]\big)$.
3. For i.i.d. adherence with $\mathbb P(\xi_n=1)=p\in(0,1)$, the relative mean concentration is $\mu^{\mathrm{single}}=p<\mu^{\mathrm{double}}=p+p(1-p)$. Under the single-dose protocol the relative root-mean-square error is $\varepsilon^{\mathrm{single}}=\sqrt{(\varepsilon^{\mathrm{perf}})^2+\eta^{\mathrm{single}}}$, with

$$(\varepsilon^{\mathrm{perf}})^2=\frac{k_ak_e\tau\big(k_a\coth\frac{k_e\tau}2-k_e\coth\frac{k_a\tau}2\big)}{2(k_a^2-k_e^2)}-1,$$

$$\eta^{\mathrm{single}}=(1-p)\,\frac{k_a^2\Big(4-k_e\tau\big(\frac4{e^{k_e\tau}-1}+1\big)\Big)+\frac{k_ak_e^2\tau\,(e^{k_a\tau}+3)}{e^{k_a\tau}-1}-4k_e^2}{2(k_a^2-k_e^2)}+(1-p)^2\,\frac{k_ak_e\tau\big(k_ae^{k_a\tau}-k_a-k_ee^{k_e\tau}+k_e\big)}{(k_a^2-k_e^2)(e^{k_a\tau}-1)(e^{k_e\tau}-1)}.$$

Here $\varepsilon$ is measured relative to the perfect-adherence average $C_0=DF/(Vk_e\tau)$. The correction $\eta^{\mathrm{single}}$ can be negative: as $p\to0$, $\varepsilon^{\mathrm{single}}\to1$, so $\eta^{\mathrm{single}}\to1-(\varepsilon^{\mathrm{perf}})^2$, which is negative when $\varepsilon^{\mathrm{perf}}>1$.
4. *(Toxicity.)* Under the single-dose protocol, the largest possible concentration over all adherence patterns equals that of perfect adherence, attained at $t^*=\tau\ln\!\big(\frac{(1-\alpha)\ln\beta}{(1-\beta)\ln\alpha}\big)/\ln(\alpha/\beta)$, so missed doses never raise the peak. Under the double-dose protocol,

$$\sup_{t\in[0,\tau],\,N\ge0,\,\xi}c^{\mathrm{double}}(N\tau+t)\le C^{\mathrm{perf}}(t^*)+b(s^*),\qquad b(s)=\kappa\big(\alpha^{s/\tau}-\beta^{s/\tau}\big),\quad s^*=\frac{\ln(k_a/k_e)}{k_a-k_e},$$

where $C^{\mathrm{perf}}(t)=\kappa\big(\alpha^{t/\tau}/(1-\alpha)-\beta^{t/\tau}/(1-\beta)\big)$ and $b(s^*)$ is the peak concentration after one dose.

## Proof sketch

The concentration at a fixed phase of the dosing cycle is a linear filter of the dose sequence with geometric weights $\alpha^n$ and $\beta^n$, which gives a perpetuity-type limit $C$. Because the filter is linear, means depend only on the long-run fraction of dose taken, and second moments depend on the two-point correlations of $f_n$. These are explicit for finite-memory protocols. Comparing $\mu,\varepsilon$ and the overshoot $\theta$ across protocols and drug parameters gives a quantitative way to design regimens that are forgiving to nonadherence. For example, a double-dose catch-up rule raises the mean exposure. Whether it also reduces the fluctuation error $\varepsilon$, and at what toxicity cost $\theta$, depends on $k_a\tau$, $k_e\tau$ and $p$.

## Sources

- Elijah D. Counterman and Sean D. Lawley, "Designing Drug Regimens that Mitigate Nonadherence", *Bulletin of Mathematical Biology* 84 (2022), 20, <https://doi.org/10.1007/s11538-021-00976-3>. Preprint version: arXiv:2108.08358 (2021), Section 2 (model and statistics $\mu,\varepsilon,\theta$), Theorem 1 (large-time limit), Theorem 2 (moments), Corollaries 3–4 (single and double dose protocols), Theorem 5 (maximum concentration), <https://doi.org/10.48550/arXiv.2108.08358>.
