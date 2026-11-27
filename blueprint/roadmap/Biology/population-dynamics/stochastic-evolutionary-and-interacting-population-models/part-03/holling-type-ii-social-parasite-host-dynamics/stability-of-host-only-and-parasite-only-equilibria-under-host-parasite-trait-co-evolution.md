# Stability of host-only and parasite-only equilibria under host–parasite trait co-evolution

**Model.** Host and parasite carry mean traits $u_1,u_2$ that set the host carrying capacity $K_1(u_1)$, the parasite carrying capacity $K_2(u_2)$, the parasitism efficiency $a(u_1,u_2)$ and the parasite death rate $d(u_2)$, all positive, bounded and smooth. With the fitness functions

$$
G_1=r_1\Big(1-\frac{x_1}{K_1(v_1)}\Big)-\frac{a(v_1,u_2)\,x_2}{1+h\,a(v_1,u_2)\,x_1},\qquad G_2=\frac{e\,a(u_1,v_2)\,x_1}{1+h\,a(u_1,v_2)\,x_1}-d(v_2)+r_2\Big(1-\frac{x_2}{K_2(v_2)}\Big),
$$

the Darwinian dynamics are $\dot x_i=x_iG_i|_{v_i=u_i}$ and $\dot u_i=\sigma_i^2\,\partial_{v_i}G_i|_{v_i=u_i}$, $i=1,2$, where $\sigma_i^2$ is the trait variance. Write $a_{u_i}$, $a_{u_iu_i}$ for partial derivatives of $a$ at $(u_1^*,u_2^*)$.

**Theorem (boundary equilibria).**

- The host-only equilibrium $(K_1(u_1^*),0,u_1^*,u_2^*)$ exists if $K_1'(u_1^*)=0$ and $d'(u_2^*)=\frac{eK_1a_{u_2}}{(1+haK_1)^2}$. It is locally asymptotically stable if

$$
0<\frac{eaK_1}{1+haK_1}<d(u_2^*)-r_2,\qquad K_1''(u_1^*)<0,\qquad \frac{eK_1\big[a_{u_2u_2}(1+haK_1)-2K_1a_{u_2}^2\big]}{(1+haK_1)^3}<d''(u_2^*),
$$

with $K_1=K_1(u_1^*)$, $a=a(u_1^*,u_2^*)$.

- The parasite-only equilibrium $\big(0,K_2(u_2^*)(1-d(u_2^*)/r_2),u_1^*,u_2^*\big)$ exists if $a_{u_1}=0$, $d(u_2^*)<r_2$ and $d'(u_2^*)=r_2K_2'(u_2^*)/K_2(u_2^*)$. It is locally asymptotically stable if

$$
\frac{r_1}{a}<K_2\Big(1-\frac{d}{r_2}\Big),\qquad a_{u_1u_1}>0,\qquad \frac{r_2\big(1-\frac d{r_2}\big)\big[K_2K_2''-2(K_2')^2\big]}{K_2^2}<d''(u_2^*).
$$

**Corollary (trait-independent death rate).** If $d$ does not depend on $u_2$: the host-only equilibrium exists if $K_1'(u_1^*)=a_{u_2}=0$ and is locally asymptotically stable if $0<\frac{eaK_1}{1+haK_1}<d-r_2$, $K_1''(u_1^*)<0$ and $a_{u_2u_2}<0$; the parasite-only equilibrium exists if $K_2'(u_2^*)=a_{u_1}=0$ and is locally asymptotically stable if $\frac{r_1}{a}<K_2(1-\frac{d}{r_2})$, $a_{u_1u_1}>0$ and $K_2''(u_2^*)<0$.

Thus stability of either one-species state requires it to be ecologically stable and, in addition, a fitness maximum in the resident's own trait. For the parasite-only state the host trait must sit at a minimum of parasitism efficiency ($a_{u_1u_1}>0$). For the modified Gaussian trait functions $K_i(v)=K_{0i}e^{-v^2(v-c)^2/(2\sigma_{K_i}^2)}$ and $a(v_1,v_2)=a_0e^{-(v_1-v_2+c)^2(v_1-v_2-c)^2/(2\sigma_a^4)}$ on $[0,c]$, one has $a_{u_1u_1}(0,0)<0$, so the parasite-only state at traits $(0,0)$ is never stable, while the host-only strategy is an ESS whenever $r_2+\frac{ea_0K_{01}}{1+a_0hK_{01}}<d$.

## Depends on

- [Persistence and one-species extinction in the obligate–facultative social parasite model](persistence-and-one-species-extinction-in-the-obligate-facultative-social-parasite-model.md)

## Expansion

At a boundary equilibrium the four-dimensional Jacobian is block triangular. The ecological block reproduces the invasion conditions of the trait-fixed model. The trait block at the host-only state is $\sigma_1^2\partial_{u_1}^2H_1=\sigma_1^2r_1K_1''/K_1$ for the host, and for the absent parasite the second derivative of $G_2$ in $v_2$, which gives the inequality on $d''$. At the parasite-only state the host trait gradient is $-\sigma_1^2x_2a_{u_1}$, so its derivative is $-\sigma_1^2x_2a_{u_1u_1}$, negative exactly when $a_{u_1u_1}>0$. Equilibrium existence requires the trait gradients to vanish, which gives the first-order conditions.

## Sources

- Yun Kang and Jennifer H. Fewell, *Co-evolutionary dynamics of a host-parasite interaction model: obligate versus facultative social parasitism*, arXiv:1505.04348 (2015), Theorem 4.1, Corollary 4.1, Theorems 4.2–4.4 (Section 4). <https://doi.org/10.48550/arXiv.1505.04348>. Published version: "Co‐evolutionary dynamics of a social parasite–host interaction model: obligate versus facultative social parasitism", Natural Resource Modeling 28(4) (2015), 398–455, <https://doi.org/10.1111/nrm.12078>; locators above refer to the arXiv version.
