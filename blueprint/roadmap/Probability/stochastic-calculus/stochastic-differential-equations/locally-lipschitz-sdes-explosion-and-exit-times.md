# Locally Lipschitz SDEs up to the exit time

Let $D=(\ell,r)$ with $-\infty\le\ell<r\le\infty$, let $b,\sigma:D\to\mathbb R$ be locally Lipschitz, let $x\in D$, and let $B$ be an $(\mathcal F_t)$-Brownian motion. Choose compact intervals $[\ell_n,r_n]\uparrow D$ with $x\in(\ell_1,r_1)$. Then there are a stopping time $\zeta$ and a continuous adapted process $X$ on $[0,\zeta)$ with values in $D$ such that, with $\tau_n=\inf\{t:X_t\notin(\ell_n,r_n)\}$,

$$\tau_n\uparrow\zeta,\qquad X_{t\wedge\tau_n}=x+\int_0^{t\wedge\tau_n}b(X_s)\,ds+\int_0^{t\wedge\tau_n}\sigma(X_s)\,dB_s\quad(t\ge0,\ n\ge1),$$

and the solution is unique: any other such pair $(X',\zeta')$ has $\zeta'=\zeta$ and $X'=X$ on $[0,\zeta)$ almost surely. The time $\zeta$ is the exit time from $D$; for $D=\mathbb R$ it is the explosion time. The solution is obtained by patching the [strong solutions for Lipschitz coefficients](../sde-lipschitz-exists-unique.md) of truncated equations and stopping at exit times of compacts.

## Depends on

- [Strong solutions of SDEs with Lipschitz coefficients](../sde-lipschitz-exists-unique.md)

## Proof depends on

- [Usual conditions and continuous-time hitting times](../../markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/usual-conditions-and-continuous-time-hitting-tim.md)

## Expansion

A full proof takes globally Lipschitz $b_n,\sigma_n$ agreeing with $b,\sigma$ on $[\ell_n,r_n]$, solves the truncated equations, shows by pathwise uniqueness that the $n$-th and $(n+1)$-th solutions agree up to $\tau_n$, and defines $X$ consistently on $[0,\zeta)$. It should also show that on $\{\zeta<\infty\}$, $X_t$ converges to $\ell$ or $r$ as $t\uparrow\zeta$, and that $\zeta$ does not depend on the choice of the compacts.

## Sources

- L. C. G. Rogers and D. Williams, *Diffusions, Markov Processes and Martingales, Volume 2: Itô Calculus*, 2nd ed., Cambridge Mathematical Library, 2000, <https://doi.org/10.1017/CBO9780511805141>, local existence up to explosion (topic).
