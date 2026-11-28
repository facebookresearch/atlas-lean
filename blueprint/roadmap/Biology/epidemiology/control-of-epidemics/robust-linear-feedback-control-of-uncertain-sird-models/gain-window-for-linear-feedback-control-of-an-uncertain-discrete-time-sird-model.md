# Gain window for linear feedback control of an uncertain discrete-time SIRD model

**Setting.** In discrete time $k=0,1,\dots$ (days) let $S,I,R,D$ be susceptible, infected, recovered and deceased counts, with $S(0)=S_0$, $I(0)=I_0>0$, $R(0)=D(0)=0$ and $I_0\delta_{\max}<S_0$. The uncertain SIRD model is

$$S(k+1)=S(k)-\delta(k)I(k),\quad I(k+1)=(1+\delta(k))I(k)-v(k)u(k)-d_I(k)I(k),$$

$$R(k+1)=R(k)+v(k)u(k),\quad D(k+1)=D(k)+d_I(k)I(k),$$

where the growth rate of undetected or asymptomatic infections $\delta(k)\in[0,\delta_{\max}]$, the control effectiveness $v(k)\in[v_{\min},v_{\max}]\subseteq(0,1]$ and the death rate $d_I(k)\in[0,d_{\max}]$, $d_{\max}<1$, are mutually independent i.i.d. sequences with arbitrary laws on these ranges (endpoints in the support). Write $\bar\delta,\bar v,\bar d_I$ for their means. The control is a linear feedback $u(k)=KI(k)$ with gain $K\ge0$, the intensity of treatment or non-pharmaceutical intervention.

**Theorem.**

1. (Almost sure control.) If $\delta_{\max}<v_{\min}(1-d_{\max})/v_{\max}$ and

$$\frac{\delta_{\max}}{v_{\min}}<K<\frac{1-d_{\max}}{v_{\max}},$$

then $I(k)/I_0\to0$ almost surely and $I(k)<I_0$ for all $k$ almost surely; at the boundary gain $K=\delta_{\max}/v_{\min}$ one still has $I(k)\le I_0$.

2. (Control in mean.) If $\bar\delta<(1-d_{\max})\bar v/v_{\max}$ and

$$\frac{\bar\delta-\bar d_I}{\bar v}<K<\frac{1-d_{\max}}{v_{\max}},$$

then $\mathbb{E}[I(k)]/I_0\to0$ and $\mathbb{E}[I(k)]\le I_0$ for all $k$; at $K=(\bar\delta-\bar d_I)/\bar v$, $\mathbb{E}[I(k)]=I_0$ for all $k$.

The lower end of each window guarantees that treatment outpaces new infections; the upper end keeps $I(k)$ nonnegative, so the control never removes more infected than exist.

## Expansion

Under linear feedback the infected count is a product of i.i.d. multipliers,

$$I(k)=I_0\prod_{j=0}^{k-1}\big(1+\delta(j)-v(j)K-d_I(j)\big).$$

If $K>\delta_{\max}/v_{\min}$, every multiplier is at most $1+\delta_{\max}-v_{\min}K<1$; if $K<(1-d_{\max})/v_{\max}$, every multiplier is positive. Almost-sure decay to zero then follows (indeed geometric decay), and the remaining compartments are recovered by telescoping sums of $I$, which are bounded because $\sum_k I(k)<\infty$. In mean, independence gives $\mathbb{E}[I(k)]=I_0(1+\bar\delta-\bar vK-\bar d_I)^k$, which decays exactly when $K>(\bar\delta-\bar d_I)/\bar v$. The quantity $\delta(k)(S+I)/S$ divided by $v(k)K+d_I(k)$ plays the role of a time-varying reproduction ratio, and the gain conditions keep it below one.

## Sources

- Chung-Han Hsieh, "On Control of Epidemics with Application to COVID-19", arXiv:2011.00790 (2020): Section 2.1 (uncertain SIRD model and assumptions), Sections 2.2–2.3 (almost sure and average control problems), Section 3.6 (linear policy), Section 4.1 (almost sure control theorem for infected cases), Section 5.1 (control theorem for expected infected cases). <https://doi.org/10.48550/arXiv.2011.00790> Published version: IEEE Access, vol. 9, pp. 167948-167958, 2021, <https://doi.org/10.1109/ACCESS.2021.3136191>.
