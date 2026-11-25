# Log-Laplace equation for the finite-type superprocess limit of critical binary branching

Let $E=\{1,\ldots,d\}$ be finite, let $A=(a_{ij})$ be a rate matrix on $E$ (nonnegative off-diagonal entries, zero row sums), acting on $u\in\mathbb R^E$ by $(Au)_i=\sum_ja_{ij}u_j$, and let $\gamma>0$. For $N\ge1$, consider a particle system in which each particle carries mass $1/N$ and a type in $E$; types move independently as Markov chains with rate matrix $A$, and each particle, at rate $N\gamma$, independently dies or splits into two particles of its type, each with probability $\tfrac12$. Let $X^N_t\in[0,\infty)^E$ be the vector of masses by type, with deterministic initial values $X^N_0\to\mu\in[0,\infty)^E$.

Assume that the laws of the vector processes $(X^N)_N$ satisfy compact containment and are C-tight in $D([0,T],[0,\infty)^E)$ for each $T$ (the vector analogue of the [scalar compact-containment and C-tightness statement](../linear-birth-death-process/compact-containment-and-c-tightness-for-critical.md)). Then every subsequential limit in law $X$ has continuous paths and, for every $f\in[0,\infty)^E$ and $t\ge0$,

$$\mathbb E_\mu\bigl[e^{-\langle f,X_t\rangle}\bigr]=e^{-\langle u_t,\mu\rangle},\qquad \frac{d}{dt}u_t=Au_t-\frac\gamma2u_t^2,\quad u_0=f,$$

where $u_t^2$ is the coordinatewise square and $\langle g,x\rangle=\sum_ig_ix_i$; the equation has a unique global solution with $u_t\ge0$. Moreover $X$ solves the martingale problem for

$$\mathcal LF(x)=\sum_{i\in E}x_i\Bigl(\frac\gamma2\,\partial_i^2F(x)+\sum_{j\in E}a_{ij}\,\partial_jF(x)\Bigr)$$

on the bounded test functions $F(x)=e^{-\langle f,x\rangle}$, $f\in(0,\infty)^E$, for which $\mathcal LF(x)=F(x)\,\bigl\langle\tfrac\gamma2f^2-Af,\,x\bigr\rangle$. Since these Laplace functionals determine the one-time laws, all subsequential limits have the same one-time marginals.

## Depends on

- [Compact containment and C-tightness for critical binary branching (concrete scaling)](../linear-birth-death-process/compact-containment-and-c-tightness-for-critical.md)
- [Global existence and uniqueness for globally Lipschitz ODEs](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md)

## Proof depends on

- [Martingale-problem limits on a locally compact state space](../../markov-chains/martingale-problems/martingale-problem-limits-on-a-locally-compact-s.md)
- [Feller branching diffusion as the scaling limit of critical binary branching](../linear-birth-death-process/feller-branching-diffusion-as-the-scaling-limit.md)
- [Non-explosion criteria and Kolmogorov equations on a countable state space](../../markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/non-explosion-criteria-and-kolmogorov-equations.md)

## Expansion

A full proof page must establish:

- The particle realization and the finite-$N$ generator acting on $e^{-\langle f,x\rangle}$, and its uniform convergence on compact sets to $\mathcal L$, as needed for [martingale-problem limits on a locally compact state space](../../markov-chains/martingale-problems/martingale-problem-limits-on-a-locally-compact-s.md).
- Global existence, uniqueness and nonnegativity of $u$ (a priori bounds $0\le u_t$ and $\max_iu_t(i)\le\max_if(i)$ reduce the quadratic equation to a globally Lipschitz one).
- The duality computation $\frac{d}{ds}\mathbb E\bigl[e^{-\langle u_{t-s},X_s\rangle}\bigr]=0$ from the martingale problem, giving the Laplace-functional identity.
- Consistency with the total mass: for $A$ with zero row sums and $f\equiv\lambda$, $u_t\equiv\lambda/(1+\gamma\lambda t/2)$, the log-Laplace function of [Feller's branching diffusion](../linear-birth-death-process/feller-branching-diffusion-as-the-scaling-limit.md).

## Sources

- A. M. Etheridge, *An Introduction to Superprocesses*, University Lecture Series 20, American Mathematical Society (2000), <https://bookstore.ams.org/ULECT/20> (construction of superprocesses as limits of branching particle systems).
- D. A. Dawson, *Measure-valued Markov processes*, in École d'Été de Probabilités de Saint-Flour XXI (1991), Lecture Notes in Mathematics 1541, Springer (1993), <https://link.springer.com/chapter/10.1007/BFb0084190>.
