# Resource concentration in colonial populations under correlated noise

**Setting.** The colonial branching diffusion of the [many-to-one formula](many-to-one-formula-for-colonial-branching-diffusions.md): colonies die at rate $\mu$, a colony of resource $x$ splits at rate $\lambda x/R_t$ into fractions $\Theta x$ and $(1-\Theta)x$ with $\Theta\sim q$ on $[0,1]$, and between events $\mathrm{d}X^u_t=aX^u_t\,\mathrm{d}t+\frac{\sigma}{\sqrt{1+\delta^2}}X^u_t(\mathrm{d}B^u_t+\delta\,\mathrm{d}W_t)$ with intrinsic noises $B^u$ and a shared environmental noise $W$. Let $N_t$ be the number of colonies, $R_t$ the total resource, $\mathbb{G}(t)$ the set of living colonies and $U_t$ a uniformly chosen colony.

**Proposition (colony number).** $N_t$ is an $M/M/\infty$ queue with arrival rate $\lambda$ and service rate $\mu$, so its law does not depend on $a,\sigma,\delta$ or $q$. Its mean extinction time from $N_0$ colonies is

$$\mathbb{E}[T_0]=\sum_{k=0}^{N_0-1}\frac{k!}{\lambda(\lambda/\mu)^k}\sum_{j\ge k+1}\frac{(\lambda/\mu)^j}{j!},$$

and $\lambda te^{-\mu t}+N_0e^{-\mu t}\le\mathbb{E}[N_t]\le f(t)+N_0e^{-\mu t}$ with $f(t)=O(1/t)$.

**Proposition (total resource).** $\mathbb{E}[R_t]=R_0e^{(a-\mu)t}$. If moreover every initial colony has resource $1$ (so $R_0=N_0$), the normalized variance $\mathrm{Var}[R_t]/(R_0^2e^{2(a-\mu)t})+1$ is bounded above by $\frac{1}{R_0}e^{(\mu+\sigma^2)t}+\frac{R_0-1}{R_0}e^{\sigma^2\delta^2t/(1+\delta^2)}$ and bounded below by

$$\frac{\mu+\frac{\sigma^2}{1+\delta^2}}{R_0\,c}\Big(e^{(\mu+\sigma^2-2\lambda\mathbb{E}[\Theta(1-\Theta)])t}-e^{\frac{\sigma^2\delta^2}{1+\delta^2}t}\Big)+e^{\frac{\sigma^2\delta^2}{1+\delta^2}t},\qquad c=\mu+\frac{\sigma^2}{1+\delta^2}-2\lambda\mathbb{E}[\Theta(1-\Theta)],$$

read by continuity when $c=0$ (the two exponents differ by exactly $ct$). The unit initial resources are needed: the source's proof (Section 4.2.4) sets $\mathbb{E}[\widehat Y_0]=1$, which is $\sum_u(X^u_0)^2/R_0$, and a single initial colony with $X_0=2$ violates the upper bound for small $t>0$.

**Proposition (sharing of resources).** As $t\to\infty$,

$$\mathbb{E}\big[\mathbf 1_{\{\mathbb{G}(t)\ne\emptyset\}}X^{U_t}_t\big]\sim R_0e^{(a-\mu)t}\,\frac{\mu}{\lambda}\big(1-e^{-\lambda/\mu}\big).$$

With $\mu,\lambda,q$ fixed:

- if $\sigma^2/(1+\delta^2)\to\infty$ (strong intrinsic noise), then for every $\varepsilon>0$, $\mathbb{E}\big[\sum_{u}X^u_t\mathbf 1_{\{X^u_t/R_t\ge1-\varepsilon\}}\big]\sim\mathbb{E}[R_t]$: almost all resource sits in one colony;
- if $\sigma^2/(1+\delta^2)\to0$, then for $1/2<\gamma<1$, with $\alpha=\lambda\mathbb{E}[\Theta(1-\Theta)]/\mu$,

$$\limsup_{t\to\infty}\frac{\mathbb{E}\big[\sum_u X^u_t\mathbf 1_{\{X^u_t/R_t\ge\gamma\}}\big]}{\mathbb{E}[R_t]}\le\frac{\sqrt{1+8\alpha}-1}{4\gamma\alpha}\xrightarrow[\alpha\to\infty]{}0,$$

so resources are spread among many colonies when fission is frequent and even.

## Depends on

- [Many-to-one formula for colonial branching diffusions](many-to-one-formula-for-colonial-branching-diffusions.md)

## Expansion

Because the fission rates $\lambda X^u/R$ sum to $\lambda$, colonies are created at constant rate $\lambda$ and removed at rate $\mu N$, which is the $M/M/\infty$ queue; noise therefore cannot change persistence, unlike models with independent colonies. The mean of $R_t$ follows from the many-to-one formula with $f\equiv$ resource. For concentration, the many-to-one formula expresses the share held by large colonies through the spine's relative weight $\widehat Y_t/\widehat R_t$: intrinsic noise makes the spine's log-resource diffuse away from the others (one colony wins), while the shared noise $W$ moves all colonies together and does not separate them; frequent balanced fission (large $\alpha$) keeps cutting the spine back.

## Sources

- Sylvain Billiard, Charles Medous, Charline Smadi, "Spinal study of a population model for colonial species with interactions and environmental noise", *Stochastic Processes and their Applications* 196 (2026), 104923, Propositions 2.3, 2.5 and 2.6 (Section 2.3), <https://doi.org/10.1016/j.spa.2026.104923> (preprint arXiv:2501.17608).
