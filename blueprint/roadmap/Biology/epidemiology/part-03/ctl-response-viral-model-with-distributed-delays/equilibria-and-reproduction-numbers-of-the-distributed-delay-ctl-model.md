# Equilibria and reproduction numbers of the distributed-delay CTL model

**Model.** Let $x,y,v,z$ be the concentrations of uninfected target cells, productively infected cells, free virus and virus-specific cytotoxic T lymphocytes (CTLs). Let $f_1$ on $[0,h_1]$ and $f_2$ on $[0,h_2]$ be nonnegative integrable delay kernels with $\int_0^{h_1}f_1=\int_0^{h_2}f_2=1$ (infection delay and virus-production delay). The Nowak–Bangham CTL model with distributed delays is

$$
\begin{aligned}
x'(t)&=s-dx(t)-kx(t)v(t),\\
y'(t)&=k_d\int_0^{h_1}f_1(\tau)x(t-\tau)v(t-\tau)\,d\tau-\delta y(t)-py(t)z(t),\\
v'(t)&=N_d\delta\int_0^{h_2}f_2(\tau)y(t-\tau)\,d\tau-\mu v(t),\\
z'(t)&=qy(t)z(t)-bz(t),
\end{aligned}
$$

with all parameters positive, $k_d\le k$ and $N_d\le N$ (survival during the delays). Initial data are continuous nonnegative histories on $[-\bar h,0]$, $\bar h=\max\{h_1,h_2\}$, and $z(0)=z_0\ge0$.

**Threshold parameters.**

$$
R_0=\frac{s\,k_dN_d}{d\mu},\qquad
R_1=\frac{s}{\dfrac{d\mu}{k_dN_d}+\dfrac{k}{k_d}\,\dfrac{\delta b}{q}},
$$

the basic reproduction numbers for viral infection and for the CTL response; always $R_1<R_0$.

**Theorem.**

1. *(Positivity and dissipativity.)* Solutions are nonnegative, and eventually bounded by a constant independent of the initial data.
2. *(Equilibria.)* The uninfected equilibrium $E_0=(s/d,0,0,0)$ always exists. If $R_0>1$ there is an infected equilibrium without immune response

$$
E_1=\Big(\frac{\mu}{k_dN_d},\ \frac{k_d}{k\delta}\Big(s-\frac{d\mu}{k_dN_d}\Big),\ \frac{k_dN_d}{k\mu}\Big(s-\frac{d\mu}{k_dN_d}\Big),\ 0\Big),
$$

and if $R_1>1$ there is an infected equilibrium with immune response

$$
E_2=\Big(x_2^*,\ \frac bq,\ \frac{N_d\delta}{\mu}\frac bq,\ \frac{\delta}{p}\Big(\frac{k_dN_dx_2^*}{\mu}-1\Big)\Big),\qquad x_2^*=\frac{s}{d+k\frac{N_d\delta}{\mu}\frac bq}.
$$

## Expansion

At $E_1$ the virus is at the level where one infected cell exactly replaces itself, so $x_1^*=\mu/(k_dN_d)$ regardless of the immune system. $E_2$ is fixed instead by the CTL balance $qy=b$, which pins $y_2^*=b/q$; the remaining coordinates follow. $R_1>1$ is exactly the condition $z_2^*>0$, i.e. that the infected-cell level $y_1^*$ sustained without immunity exceeds the CTL activation threshold $b/q$. Boundedness follows from the functional $G=\frac{k_d}{k}\int_0^{h_1}f_1(\tau)x(t-\tau)d\tau+y+\frac pqz$, which satisfies $G'\le sk_d/k-\min\{d,\delta,b\}G$.

## Sources

- Yukihiko Nakata, "Global dynamics of cell mediated immunity in viral infection models with distributed delays", arXiv:1008.2518 (2010), Section 2 (positivity and boundedness lemma; reproduction numbers $R_0,R_1$; existence theorem for $E_0,E_1,E_2$), <https://doi.org/10.48550/arXiv.1008.2518>.
