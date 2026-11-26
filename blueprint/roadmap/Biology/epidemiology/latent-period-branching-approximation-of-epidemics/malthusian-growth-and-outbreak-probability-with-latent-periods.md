# Malthusian growth, outbreak probability and the early branching phase of an epidemic with latent periods

**Model.** In a large homogeneous population each infected individual has a latent time $Y$ followed by an infectious time $X$ (jointly distributed, continuous, with finite moments), during which it makes contacts as a Poisson process of rate $\lambda$; early on every contact infects a new susceptible. Let $L_\cdot$ denote Laplace transforms. Then:
- $R_0=\lambda\,\mathbb E(X)$;
- the *generation time density* is $g(t)=\mathbb P(Y<t<X+Y)/\mathbb E(X)$, with $L_g(s)=\big(L_Y(s)-L_{X+Y}(s)\big)/\big(s\,\mathbb E X\big)$;
- for $R_0>1$ the **Malthusian parameter** $\alpha>0$ is the unique root of $R_0L_g(\alpha)=1$, equivalently $\alpha=\lambda\big(L_Y(\alpha)-L_{X+Y}(\alpha)\big)$;
- the probability $p$ of a major outbreak is the positive root of $1-p=L_X(\lambda p)$, and the final size $\pi$ of a major outbreak solves $-\ln(1-\pi)=R_0\pi$.

**Theorem (growth rate versus outbreak probability).** For $R_0>1$,

$$\frac{p\lambda}{\alpha}\ge1,$$

with equality if and only if $Y\equiv0$ (no latent period).

**Theorem (branching phase).** Let $B(t)$ be the number infected by time $t$ in the approximating branching process started by one case, $M(t)=\mathbb E B(t)$ and $Z(t)=B(t)e^{-\alpha t}$. Then $M$ solves the renewal equation $M(t)=R_0\big(G(t)+\int_0^tg(s)M(t-s)\,ds\big)$, $M(t)\le Ke^{\alpha t}$ for some constant $K$, and

$$\lim_{t\to\infty}\mathbb E\,Z(t)=-\frac{1}{\alpha R_0L_g'(\alpha)} .$$

Moreover the Laplace transform $L_Z(s)=\lim_{t\to\infty}\mathbb E e^{-sZ(t)}$ of the limit $Z(\infty)$ is the solution, with that mean, of

$$L_Z(s)=\int_0^\infty\!\!\int_0^\infty\exp\Big(-\lambda\Big(x-\int_y^{y+x}L_Z\big(se^{-\alpha u}\big)\,du\Big)\Big)f_{YX}(y,x)\,dy\,dx .$$

The limit $Z(\infty)$ has an atom $1-p$ at zero (minor outbreak), and on a major outbreak the epidemic behaves like $Z(\infty)e^{\alpha t}$ until a non-negligible fraction is infected, after which a deterministic differential-equation approximation takes over with a random time shift set by $Z(\infty)$.

## Expansion

Since $\alpha=\lambda\,\mathbb E\big[e^{-\alpha Y}(1-e^{-\alpha X})\big]$ and $p=1-\mathbb E e^{-\lambda pX}$, the inequality compares $\mathbb E[e^{-\alpha Y}(1-e^{-\alpha X})]/\alpha$ with $\mathbb E[1-e^{-\lambda pX}]/(\lambda p)$; the function $u\mapsto(1-e^{-uX})/u$ is decreasing, and the factor $e^{-\alpha Y}\le1$ only lowers the left side, which gives $\alpha\le p\lambda$ with equality exactly when $Y=0$. The renewal equation follows from conditioning on the first case's $(Y,X)$ and its Poisson contacts; taking Laplace transforms and applying the key renewal theorem gives the limit of $\mathbb E Z(t)$, and the regenerative structure gives the functional equation for $L_Z$. When two strains with different growth rates are introduced together, each first grows as an independent branching process, and the random shifts $Z_1(\infty),Z_2(\infty)$ determine how immunity from the faster strain limits the final size of the slower one.

## Sources

- Åke Svensson, "On a stochastic model of epidemic spread with an application to competing infections", arXiv:1805.10677 (2018): Section 2.1 (notation and relations), Theorem 2.1, Theorem 3.1, Corollary 3.1, Theorem 3.2, Sections 4–6. <https://doi.org/10.48550/arXiv.1805.10677>
