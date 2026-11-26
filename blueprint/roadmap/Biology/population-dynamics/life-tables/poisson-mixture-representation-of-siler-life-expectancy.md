# Poisson mixture representation of Siler life expectancy

**Siler model.** Age at death $T$ has hazard $\mu(t)=a_1e^{-b_1t}+a_2+a_3e^{b_3t}$ with $a_1,a_2\ge0$ and $a_3,b_1,b_3>0$ (declining immaturity, constant background and Gompertz senescence components). For a survivor at age $x$ put

$$A_x=\frac{a_1e^{-b_1x}}{b_1},\qquad G_x=\frac{a_3e^{b_3x}}{b_3},$$

so the remaining-lifetime survival is ${}_tp_x=\exp\{-A_x(1-e^{-b_1t})-a_2t-G_x(e^{b_3t}-1)\}$ and $e_x=\int_0^\infty{}_tp_x\,dt$. Let $e^{\mathrm{GM}}_x(c)=\int_0^\infty\exp\{-ct-G_x(e^{b_3t}-1)\}dt=\frac{e^{G_x}}{b_3}E_{1+c/b_3}(G_x)$ be the Gompertz-Makeham remaining life expectancy with Makeham term $c$, where $E_s(z)=\int_1^\infty e^{-zw}w^{-s}dw$ is the generalized exponential integral.

**Proposition (distributional mixture).** For all $x,t\ge0$,

$${}_tp_x=\mathbb{E}\Big[\exp\{-(a_2+b_1K_x)t-G_x(e^{b_3t}-1)\}\Big],\qquad K_x\sim\mathrm{Poisson}(A_x).$$

So the Siler remaining lifetime at age $x$ is a Poisson mixture of Gompertz-Makeham remaining lifetimes with Makeham term $a_2+b_1K_x$.

**Corollary (series for $e_x$).** With $w_n(x)=e^{-A_x}A_x^n/n!$ and $Q_n(x)=e^{\mathrm{GM}}_x(a_2+nb_1)$,

$$e_x=\sum_{n\ge0}w_n(x)Q_n(x)=\frac{e^{G_x-A_x}}{b_3}\sum_{n\ge0}\frac{A_x^n}{n!}E_{1+(a_2+nb_1)/b_3}(G_x).$$

**Truncation bound.** $Q_n(x)$ is nonincreasing in $n$ with $Q_n(x)\le1/(a_2+nb_1)$ when $a_2+nb_1>0$. Hence the partial sums $e^{(m)}_x=\sum_{n=0}^mw_n(x)Q_n(x)$ increase to $e_x$ and

$$0\le e_x-e^{(m)}_x\le\frac{\Pr(K_x>m)}{a_2+(m+1)b_1}.$$

## Expansion

The identity $e^{-A(1-e^{-b_1t})}=\mathbb{E}[e^{-b_1Kt}]$ for $K\sim\mathrm{Poisson}(A)$ is the Poisson probability generating function at $e^{-b_1t}$. It reads the immaturity hazard as latent clocks: a newborn carries $\mathrm{Poisson}(A_0)$ clocks, each killing at constant rate $b_1$; survival to age $x$ tilts the clock count to $\mathrm{Poisson}(A_x)$, and the population immaturity hazard $b_1\mathbb{E}K_x=a_1e^{-b_1x}$ declines by selection although no individual hazard declines. Integrating in $t$ term by term (monotone convergence) gives the series; each term is closed form via $E_s$. Because $Q_n\le1/(a_2+nb_1)$, the tail is controlled by a Poisson tail probability, and in adult ages $A_x$ is tiny so one or two terms suffice. The same argument works with any adult hazard $h$ in place of the Gompertz term, for example the gamma-Gompertz hazard.

## Sources

- Silvio C. Patricio, "An Exact Poisson Mixture Representation of Siler Remaining Life Expectancy", arXiv:2611.06376 (2026), Proposition 1, Corollary 1, Lemma 1 and Proposition 2; Corollaries 2-3 for general and gamma-Gompertz adult hazards, <https://doi.org/10.48550/arXiv.2611.06376>
