# Order-statistics law of detectable metastasis sizes

**Model.** Time is measured from disease onset at age $T$. The primary tumor size is $\Phi(t) = \Phi_0(t)$ for $0 \le t \le V - T$ and $\Phi(t) = \Phi_1(t-(V-T))\,\Phi_0(V-T)$ afterwards, where treatment starts at age $V$, $\Phi_0$ is continuous, strictly increasing with $\Phi_0(0) = 1$, and $\Phi_1 \equiv 0$ for a resected, non-recurrent primary; observing size $S$ at age $V$ gives $T = V - \varphi(S)$ with $\varphi = \Phi_0^{-1}$. Metastases are shed by a Poisson process with rate $\mu(t) = \alpha\,\Phi(t)^\theta$ ($\alpha > 0$, $\theta \ge 0$), each founds a viable metastasis in a given site independently with probability $q$, and after an i.i.d. latency with density $f$ and distribution function $F$ it starts growing from one cell. A metastasis of age $y$ has size $\Psi(y) = \Psi_1(y)$ for $0 \le y \le W - V$ and $\Psi(y) = \Psi_0(y - (W-V))\,\Psi_1(W-V)$ for $W - V < y \le W - T$, where $W > V$ is the age at observation and $\Psi_0,\Psi_1$ are strictly increasing, differentiable, with $\Psi_0(0) = \Psi_1(0) = 1$; let $\psi = \Psi^{-1}$, $M = \Psi_0(V-T)\,\Psi_1(W-V)$, and let $m$ be the detection threshold. Metastases do not seed further metastases.

**Theorem.** For a primary tumor resected at age $V$, the ordered sizes $X_1 < \cdots < X_n$ of the metastases detectable in a given site at age $W$, conditional on their number $n$, are distributed as the order statistics of an i.i.d. sample of size $n$ from the density

$$p(x) = \omega\big(W - T - \psi(x)\big)\,\psi'(x),\qquad m \le x \le M,$$

and $p(x) = 0$ otherwise, where for $0 \le t \le W - T - \psi(m)$

$$\omega(t) = \frac{\int_0^{\min\{t,\,V-T\}} \Phi(s)^\theta\, f(t-s)\,ds}{\int_0^{\min\{W-T-\psi(m),\,V-T\}} \Phi(s)^\theta\, F\big(W-T-\psi(m)-s\big)\,ds}.$$

The law is free of $\alpha$, $q$ and $n$. For $\theta = 0$ it does not depend on primary tumor growth:

$$\omega(t) = \frac{F(t) - F(\max\{0,\,t - V + T\})}{\int_0^{\min\{W-T-\psi(m),\,V-T\}} F\big(W-T-\psi(m)-s\big)\,ds}.$$

The total number of viable metastases in the site at age $t$ is Poisson with mean

$$E(t) = q\alpha\int_0^{\min\{t-T,\,V-T\}} \Phi(s)^\theta\, F(t-T-s)\,ds,$$

so the probability of having at least one is $1 - e^{-E(t)}$.

## Depends on

- [Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md)

## Proof depends on

- [Thinning of a Poisson process](../../../Probability/point-processes/poisson-processes/thinning.md)

## Expansion

Thinning by $q$ and independent delays by the latency keep the inception process Poisson, with intensity $\lambda(t) = \int_0^t q\mu(s) f(t-s)\,ds$. Conditional on the number of points in a window, the points of a Poisson process are i.i.d. with density proportional to the intensity, which gives the order-statistics representation; the constants $q\alpha$ cancel in the normalization. A metastasis is detectable at $W$ iff its age $W - T - Y$ exceeds $\psi(m)$, and the change of variables $x = \Psi(W - T - y)$ produces the Jacobian $\psi'(x)$. Fitting this likelihood to metastasis volumes measured on one scan lets the growth law before treatment ($\Psi_0$) and after it ($\Psi_1$) be compared; fitted to 12 prostate cancer patients with bone metastases, the model placed the inception of most surveyed metastases before treatment, found a nearly constant shedding rate, and estimated that surgery and chemotherapy increased the average metastatic growth rate many-fold.

## Sources

- L. Hanin, M. Zaider, "Effects of surgery and chemotherapy on metastatic progression of prostate cancer: evidence from the natural history of the disease reconstructed through mathematical modeling", Cancers 3:3632–3660 (2011), Section 3 (Eqs (1)–(3)), Section 4 (Eqs (4)–(10), Theorem 1), <https://doi.org/10.3390/cancers3033632>, PMCID PMC3759214.
