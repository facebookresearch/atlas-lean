# Persistence and one-species extinction in the obligate–facultative social parasite model

For host density $x_1$ and parasite density $x_2$, consider

$$
\begin{aligned}
\dot x_1&=x_1\Big[r_1\Big(1-\frac{x_1}{K_1}\Big)-\frac{a\,x_2}{1+h\,a\,x_1}\Big],\\
\dot x_2&=x_2\Big[\frac{e\,a\,x_1}{1+h\,a\,x_1}-d+r_2\Big(1-\frac{x_2}{K_2}\Big)\Big],
\end{aligned}
$$

with $r_1,K_1,K_2,a,h,e>0$, $r_2\ge0$, $d\ge0$. Here $a$ is parasitism efficiency, $h$ handling time, $e$ conversion efficiency, and $d$ the parasite death rate from searching for and attacking hosts. The parasite is **obligate** if $d>r_2$ (it dies out without this host) and **facultative** if $d<r_2$.

**Boundary equilibria.** $E_{00}=(0,0)$ is a saddle if $r_2<d$ and a source if $r_2>d$. $E_{10}=(K_1,0)$ is locally asymptotically stable if $r_2+\frac{eaK_1}{1+ahK_1}<d$ and a saddle if the inequality is reversed. If $r_2>d$, $E_{01}=\big(0,K_2(1-d/r_2)\big)$ exists; it is locally asymptotically stable if $\frac{r_1}{a}<K_2\big(1-\frac d{r_2}\big)$ and a saddle if $\frac{r_1}{a}>K_2\big(1-\frac d{r_2}\big)$.

**Theorem (persistence).** The host is persistent if $d>r_2$ or $\frac{r_1}{a}>K_2\big(1-\frac{d}{r_2}\big)>0$. The parasite is persistent if $r_2+\frac{eaK_1}{1+ahK_1}>d$. The system is permanent if either

$$
r_2+\frac{eaK_1}{1+ahK_1}>d>r_2\qquad\text{or}\qquad \frac{r_1}{a}>K_2\Big(1-\frac{d}{r_2}\Big)>0 .
$$

**Theorem (global extinction of one species).** If $d>r_2+\frac{eaK_1}{1+ahK_1}$, the host-only equilibrium $(K_1,0)$ is globally stable (the parasite dies out). If $\frac{r_1}{a}<K_2\big(1-\frac d{r_2}\big)$ and one of

1. $a^2r_2K_1K_2\big(h+\frac{d}{r_2}-\frac{e}{r_2}\big)>\frac{r_1r_2(ahK_1+1)^2}{3}$, or
2. $K_1<\frac{1}{ah}$, or
3. $K_1>\frac{1}{ah}$ and $\frac{r_1(1+ahK_1)^2}{4a^2hK_1K_2}<1-\frac{d}{r_2}$

holds, the parasite-only equilibrium $\big(0,K_2(1-d/r_2)\big)$ is globally stable (the host dies out). So a very large search death rate eliminates the parasite, while a facultative parasite with very small $d$ can drive the host extinct. Depending on parameters there are zero to three interior equilibria, allowing bistability.

## Expansion

Local stability at the boundary follows from the Jacobian's triangular structure there: at $(K_1,0)$ the parasite's invasion rate is $\frac{eaK_1}{1+ahK_1}-d+r_2$, and at $(0,K_2(1-d/r_2))$ the host's invasion rate is $r_1-aK_2(1-d/r_2)$. Persistence follows from these invasion rates together with the simple boundary dynamics (logistic growth on each axis). Interior equilibria are roots of a cubic obtained by eliminating $x_2$ from the host nullcline $x_2=\frac{r_1}{a}(1-x_1/K_1)(1+ahx_1)$; the listed conditions rule out positive roots, so no interior equilibrium exists and the trajectories, bounded in $[0,K_1]\times[0,K_2(r_2+e/h)/r_2]$, converge to the only stable boundary equilibrium.

## Sources

- Yun Kang and Jennifer H. Fewell, *Co-evolutionary dynamics of a host-parasite interaction model: obligate versus facultative social parasitism*, arXiv:1505.04348 (2015), Lemma 3.1, Proposition 3.1, Theorems 3.1–3.3. <https://doi.org/10.48550/arXiv.1505.04348>. Published version: "Co‐evolutionary dynamics of a social parasite–host interaction model: obligate versus facultative social parasitism", Natural Resource Modeling 28(4) (2015), 398–455, <https://doi.org/10.1111/nrm.12078>; locators above refer to the arXiv version.
