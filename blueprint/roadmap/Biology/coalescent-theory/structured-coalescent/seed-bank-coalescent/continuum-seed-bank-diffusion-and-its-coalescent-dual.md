# Continuum seed-bank diffusion and its coalescent dual

**Model.** Let $\mu$ be a finite Borel measure on $(0,\infty)$ with total mass $c>0$ and $c'=\int\lambda\,\mu(d\lambda)<\infty$. Seed-banks are labelled by their exit rate $\lambda\in(0,\infty)$; active individuals enter dormancy at total rate $c$, choosing bank $\lambda$ according to $\mu(d\lambda)/c$, and seeds in bank $\lambda$ resuscitate at rate $\lambda$. The *continuum seed-bank diffusion* $(X_t,Y_t(\lambda))$ for the frequency $X_t$ of an allele among active individuals and $Y_t(\lambda)$ in bank $\lambda$ solves
$$dX_t=\Big(\int_{(0,\infty)}Y_t(\lambda)\,\mu(d\lambda)-cX_t\Big)dt+\sqrt{X_t(1-X_t)}\,dW_t,\qquad dY_t(\lambda)=\lambda\big(X_t-Y_t(\lambda)\big)dt,$$
with $(X_0,Y_0)\in[0,1]\times\{y:0\le y\le1\ \mu\text{-a.e.}\}$. Eliminating $Y$ gives the non-Markovian stochastic Volterra equation
$$X_t=g(t)+c\int_0^tK(t-s)X_s\,ds-c\int_0^tX_s\,ds+\int_0^t\sqrt{X_s(1-X_s)}\,dW_s,\qquad K(t)=\int(1-e^{-\lambda t})\,\tfrac{\mu}{c}(d\lambda),$$
where $K$ is the distribution function of the dormancy time. For $\mu=\Gamma(a,b)$, $K(t)=1-(1+t/b)^{-a}$ is a Pareto-type law, so dormancy can be heavy-tailed.

**Theorem.**
1. *(Well-posedness.)* The equation, viewed as a stochastic evolution equation on $\mathbb R\times L^1(\mu)$, has a unique continuous strong solution, and $\mathbb E\sup_{t\le T}\|Z^1_t-Z^2_t\|\le C\,\mathbb E\|Z^1_0-Z^2_0\|$ for two solutions; with the measure-valued seed-bank component $Y_t.\mu$ in the weak-$\star$ topology it is a strong Markov (Feller) process.
2. *(Scaling limit.)* It is the limit in distribution, under time scaling by the active population size, of allele-frequency processes of discrete-time Wright–Fisher models with finitely many seed-banks and multinomial exchange between the active population and the banks.
3. *(Duality.)* Let $(N_t,M_t)$ be the Markov jump process with $N_t\in\mathbb N_0$ active lineages and a finite integer-valued measure $M_t=\sum_iM_{i,t}\delta_{\Lambda_{i,t}}$ of dormant lineages, where pairs of active lineages coalesce at rate $1$ each, each active lineage becomes dormant in bank $\lambda$ at rate $\mu(d\lambda)$, and each dormant lineage in bank $\lambda$ becomes active at rate $\lambda$. Then for $(N_0,M_0)=(n,\sum_im_i\delta_{\lambda_i})$,
$$\mathbb E\Big[X_t^n\prod_iY_t(\lambda_i)^{m_i}\Big]=\mathbb E\Big[x^{N_t}\prod_iy(\Lambda_{i,t})^{M_{i,t}}\Big].$$
$(N,M)$ is the block-counting process of the *continuum seed-bank coalescent*, which is also the scaling limit of the ancestral processes of the discrete models.

## Depends on

- [Wright–Fisher diffusion with a strong seed bank](wright-fisher-diffusion-with-a-strong-seed-bank.md)

## Expansion

When $\mu=c\,\delta_{K'}$ the model is the strong seed-bank diffusion with a single exponentially distributed dormancy time, and when $\mu$ is a finite or countable sum of atoms it is the model with "coloured" seed-banks; the continuum version realizes any completely monotone dormancy-time distribution through the Bernstein–Widder representation $1-K(t)=\int e^{-\lambda t}\mu(d\lambda)/c$, giving a Markovian lift of the Volterra equation. The dual rates are read off by applying the generator to the moment functions $x^n\prod y(\lambda_i)^{m_i}$: the diffusion term produces $\binom n2$ coalescences, the drift $\int y\,d\mu-cx$ moves an active lineage into a bank chosen by $\mu$, and $\lambda(x-y(\lambda))$ wakes a dormant lineage at rate $\lambda$. Since the state space is not locally compact unless $\mu$ is discrete, tightness is proved in the weak-$\star$ topology on measures.

## Sources

- L. Jiao, "Wright-Fisher diffusion and coalescent with a continuum of seed-banks", arXiv:2307.07110 (2023), Section 1 (equations for the diffusion and the Volterra form, Theorems 1–3), Section 5 (scaling limit) and Section 6 (continuum seed-bank coalescent), <https://doi.org/10.48550/arXiv.2307.07110>.
