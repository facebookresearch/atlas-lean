# Fixation probability and risk-dominant life-history speed

**Setting.** In the quasi-neutral chemostat with mass-mortality events, let $W_t$ be the limiting frequency jump-diffusion of type 1 on the manifold $\Gamma$ of ecological equilibria, with absorption times $\tau_i=\inf\{t:W_t=i\}$ and fixation probability $\theta(w)=\mathbb P(\tau_1<\tau_0\mid W_0=w)$. Assume catastrophes are indiscriminate: the survival vector is $\mathbf U=(1,1)U^*$ with $U^*$ supported on $[a,1]$, $a>0$ (assumption H1). Let $\kappa$ be the catastrophe rate, $\nu=\beta_i/\mu_i$ the common lifetime reproductive success and $\mathcal E_\Gamma=(F\circ R^*)^{-1}(1/\nu)$.

**Theorem 10.** If $\beta_1=\beta$ and $\beta_2=\beta+\varepsilon$ ($\varepsilon$ of either sign), then uniformly in $w\in[0,1]$

$$\theta(w)=w+\varepsilon\,w(1-w)\left[\frac{1}{2\beta}-\frac{\kappa\nu\mathcal E_\Gamma}{2\beta^3}\,\mathbb E\log\frac{1}{U^*}\right]+o(\varepsilon).$$

**Risk-dominant speed (Section 9.1).** Type $\beta$ is favored over $\beta+\varepsilon$ (a rare invader of one type replaces the other more easily than conversely, $\theta(w)\ge1-\theta(1-w)$ for small $w$) for small $\varepsilon>0$ iff $\beta^2\ge\nu\mathcal E_\Gamma\kappa\,\mathbb E\log(1/U^*)$, and for small $\varepsilon<0$ iff the reverse inequality holds. Hence

$$\beta^*=\sqrt{\nu\,\mathcal E_\Gamma\,\kappa\,\mathbb E\log(1/U^*)}$$

is evolutionarily attractive, increasing in the frequency and severity of catastrophes.

## Depends on

- [Jump-diffusion limit on the quasi-neutral manifold](jump-diffusion-limit-on-the-quasi-neutral-manifold.md)

## Expansion

$\theta$ solves $\mathbf A^\varepsilon\theta=0$ with $\theta(0)=0$, $\theta(1)=1$. At $\varepsilon=0$ the generator is $a_{1,2}w(1-w)f''$ with $a_{1,2}=\beta^2/(\nu\mathcal E_\Gamma)$, so $\theta_0(w)=w$. Linearizing in $\varepsilon$ (Lemma 11) gives $\tilde{\mathbf A}^\varepsilon f=w(1-w)[a_{1,2}f''+\varepsilon a_{2,1}f'+\varepsilon a_{2,2}f'']$ with $a_{2,1}=\beta/(\nu\mathcal E_\Gamma)-(\kappa/\beta)\mathbb E\log(1/U^*)$; solving the first-order correction yields the bracket $a_{2,1}/(2a_{1,2})$. Demographic noise alone ($\kappa=0$) favors slower types; each catastrophe opens a transient resource surplus in which faster types regrow first, contributing the negative term.

## Sources

- É. Martin, D. Steinsaltz, "Evolution of Fast and Slow Life Histories in Resource-Constrained Populations with Mass-Mortality Events", arXiv preprint (2026), Theorem 10, Lemma 11 and the risk-dominance discussion of Section 9.1, <https://doi.org/10.48550/arXiv.2609.14597>.
