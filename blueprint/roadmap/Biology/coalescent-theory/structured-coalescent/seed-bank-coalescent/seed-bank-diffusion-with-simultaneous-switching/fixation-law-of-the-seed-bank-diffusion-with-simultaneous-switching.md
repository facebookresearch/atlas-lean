# Duality and fixation law of the seed bank diffusion with simultaneous switching

**Model.** Let $X_t$ and $Y_t$ be the frequencies of an allele among active individuals and in the dormant seed bank. Fix spontaneous switching intensities $c,\bar c>0$, a relative seed-bank size constant $K>0$, simultaneous-switching fractions $z,\bar z\in(0,1)$, and rates $r_F,r_D>0$. The *seed bank diffusion with fixed-size jumps* is the jump diffusion on $[0,1]^2$ with generator

$$\begin{aligned} Af(x,y)={}&r_F\big[f(x+z(y-x),y)-f(x,y)\big]+r_D\big[f(x,y+\bar z(x-y))-f(x,y)\big]\\ &+c(y-x)\partial_xf+\bar cK(x-y)\partial_yf+\tfrac12x(1-x)\partial_x^2f . \end{aligned}$$

The jumps model rare large events: a "forest fire" in which a fraction $z$ of the active population is replaced by resuscitated seeds, and a "drought" in which a fraction $\bar z$ of the seed bank is replaced by fresh active offspring. It is the scaling limit, on the time scale $N$, of a Wright–Fisher model with $N$ active and $M$ dormant individuals in which such events occur with probability $O(1/N)$ per generation.

**Theorem (moment duality).** Let $(N_t,M_t)$ be the block-counting process of the seed bank coalescent with simultaneous switching: active lineages pairwise coalesce at rate $1$, single lineages move active $\to$ dormant at rate $c$ and dormant $\to$ active at rate $\bar cK$, at rate $r_F$ (a forest fire, read backward) each active lineage independently becomes dormant with probability $z$, and at rate $r_D$ (a drought, read backward) each dormant lineage independently becomes active with probability $\bar z$. Then for all $(x,y)\in[0,1]^2$, $n,m\in\mathbb N_0$ and $t\ge0$,

$$\mathbb E_{x,y}\big[X_t^nY_t^m\big]=\mathbb E^{n,m}\big[x^{N_t}y^{M_t}\big].$$

**Theorem (fixation in law).** As $t\to\infty$, every mixed moment $\mathbb E_{x,y}[X_t^nY_t^m]$, $n,m\in\mathbb N$, converges to the same limit $p(x,y)$, and

$$(X_t,Y_t)\Rightarrow p(x,y)\,\delta_{(1,1)}+\big(1-p(x,y)\big)\,\delta_{(0,0)},\qquad p(x,y)=\frac{(\bar cK+r_D\bar z)\,x+(c+r_Fz)\,y}{c+\bar cK+r_Fz+r_D\bar z}.$$

With $r_F=r_D=1$ this is $p=\dfrac{(\bar cK+\bar z)x+(c+z)y}{c+\bar cK+z+\bar z}$.

## Depends on

- [Seed-bank coalescent](../seed-bank-coalescent-active-dormant-lineages.md)
- [Wright–Fisher diffusion with a strong seed bank](../wright-fisher-diffusion-with-a-strong-seed-bank.md)

## Expansion

Duality is checked on monomials: applying $A$ to $x^ny^m$ in the $(x,y)$ variables gives the generator of the block-counting process applied to $x^ny^m$ in the $(n,m)$ variables; the jump terms correspond to binomial thinning of lineages. The dual is absorbed in $(1,0)$ or $(0,1)$ almost surely, so all moments converge to a common limit and the limit law is supported on $\{(0,0),(1,1)\}$. The fixation probability is the stationary value of the martingale $aX_t+bY_t$, where $a(c+r_Fz)=b(\bar cK+r_D\bar z)$ balances the drift and mean jump of the two coordinates. Large simultaneous switching events therefore shift fixation weight toward the subpopulation that receives migrants in bulk.

## Sources

- Jochen Blath, Adrián González Casanova, Noemi Kurt and Maite Wilke-Berenguer, *The seed bank coalescent with simultaneous switching*, Electron. J. Probab. 25 (2020), 1–21. <https://doi.org/10.1214/19-EJP401> Model A (Section 1.1), Theorem 1.4 (limiting generator), Definition 1.7, Theorem 1.12 (duality), Proposition 1.14 and Corollary 1.15 (moment limits and fixation in law). Locators use the numbering of the preprint arXiv:1812.03783.
