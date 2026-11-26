# Fractional-linear bounds on Galton–Watson survival probabilities

**Setting.** Let $\varphi$ be the offspring probability generating function of a supercritical Galton–Watson process, with mean $m=\varphi'(1)>1$ and ultimate extinction probability $P_\infty\in(0,1)$, the smallest root of $\varphi(x)=x$. Let $P^{(n)}=\varphi^{(n)}(0)$ be the probability of extinction by generation $n$, $S^{(n)}=1-P^{(n)}$ the probability of survival to generation $n$, $S_\infty=1-P_\infty$, and

$$\gamma=\varphi'(P_\infty)\in(0,1),$$

the geometric rate at which $P^{(n)}\uparrow P_\infty$. A fractional linear pgf $\varphi_{FL}(x;\pi,\rho)$ has iterates in closed form; there is a unique one with $\varphi_{FL}(P_\infty)=P_\infty$ and $\varphi_{FL}'(P_\infty)=\gamma$, whose iterates are $\varphi_{FL}^{(n)}(0)=\frac{P_\infty(1-\gamma^n)}{1-\gamma^nP_\infty}$.

**Basic result (proposition of Section 3.1).** If $\varphi_{FL}(x)\le\varphi(x)$ for all $x\in[0,P_\infty]$, then for every $n$

$$\frac{P_\infty(1-\gamma^n)}{1-\gamma^nP_\infty}\le P^{(n)}\le P_\infty,\qquad\text{equivalently}\qquad S_\infty\le S^{(n)}\le\frac{S_\infty}{1-\gamma^n(1-S_\infty)}.$$

**Comparison theorems (Section 4).**
- Poisson offspring with mean $m>1$: $\varphi_{FL}\le\varphi_{\rm Poi}$ on $[0,1]$, with equality only at $P_\infty$ and $1$, so the bounds hold for every $n$.
- Binomial offspring $\mathrm{Bin}(k,p)$ with $k\ge2$, parameterized by its extinction probability $\xi\in(0,1)$ via $p=(1-\xi)/(1-\xi^k)$: $\varphi_{FL}\le\varphi_{\rm Bin}$ on $[0,1]$, with equality iff $x=\xi$ or $x=1$.
- Negative-binomial offspring with $r\ge2$, parameterized by its extinction probability $\zeta$: $\varphi_{FL}\le\varphi_{\rm NB}$ on $[0,P_\infty]$, with equality iff $x=P_\infty$.
- For offspring numbers in $\{0,1,2,3\}$ the comparison holds for some distributions and fails for others; an explicit inequality on $p_0$ in terms of $p_2,p_3$ characterizes when the lower bound on $P^{(n)}$ holds for all $n$.

## Depends on

- [Haldane's survival probability](../haldane-s-survival-probability-of-a-beneficial-m/survival-prob.md)

## Expansion

Seneta's comparison argument: pgfs are increasing, so $\varphi_{FL}\le\varphi$ on $[0,P_\infty]$ propagates through iteration to $\varphi_{FL}^{(n)}(0)\le\varphi^{(n)}(0)$, and the explicit iterates of the fractional linear map give the lower bound. Matching both the fixed point and its slope makes the bound converge to $P_\infty$ at the true rate $\gamma^n$; Section 4.1.1 compares it with Pollak's and Agresti's bounds for Poisson offspring. Each comparison theorem amounts to showing that $\varphi-\varphi_{FL}$, which vanishes to second order at $P_\infty$, keeps one sign on the relevant interval. Under weak selection, where $m=1+s$, these bounds control how quickly the survival probability of a new beneficial mutation approaches Haldane's $2s$, and they transfer to fixation probabilities in the Wright–Fisher model (Section 5.4).

## Sources

- R. Bürger, "Bounds for survival probabilities in supercritical Galton-Watson processes and applications to population genetics", arXiv preprint (2025), the basic proposition of Section 3.1, the comparison theorems and corollaries of Sections 4.1–4.4, and Section 5, <https://doi.org/10.48550/arXiv.2503.21403>.
