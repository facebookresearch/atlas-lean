# Total variation bound between moment-matched size-dependent and controlled branching processes

**Setting.** Let $(Z_n)$ be a population-size-dependent branching process with offspring mean $m(z)$ and variance $\sigma^2(z)$, and let $(\widetilde Z_n)$ be a deterministically controlled branching process (DCBP), $\widetilde Z_n=\sum_{i=1}^{\phi(\widetilde Z_{n-1})}\widetilde\xi_{n,i}$ with deterministic $\phi:\mathbb N_0\to\mathbb N_0$ and offspring mean $\widetilde m$ and variance $\widetilde\sigma^2>0$. Their one-step conditional means and variances agree (*matching moments*) if and only if

$$z\,m(z)=\widetilde m\,\phi(z),\qquad z\,\sigma^2(z)=\widetilde\sigma^2\,\phi(z)\qquad(z\in\mathbb N_0).$$

A PSDBP matching a given DCBP exists if and only if $\widetilde\sigma^2\phi(z)/z\ge d(z)(1-d(z))$ for all $z\ge1$, where $d(z)$ is the fractional part of $\widetilde m\,\phi(z)/z$ (an integer-valued law with mean $\mu$ has variance at least $\{\mu\}(1-\{\mu\})$).

Assume, with $\widetilde\rho=\mathbb E|\widetilde\xi-\widetilde m|^3$ and $\rho(x)=\mathbb E|\xi(x)-m(x)|^3$:

- (C1) $\phi(x)\ge hx$ for all $x\ge1$, for some $h>0$;
- (C2) $\widetilde\rho\vee\rho(x)\le R$ for all $x\ge1$;
- (C3) for some $\eta>0$, every $x\ge1$ has an $n_x\ge1$ with $\mathbb P(\xi(x)=n_x)\wedge\mathbb P(\xi(x)=n_x-1)\ge2\eta$, and some $n\ge1$ has $\mathbb P(\widetilde\xi=n)\wedge\mathbb P(\widetilde\xi=n-1)\ge2\eta$ (each of the two consecutive integers carries mass at least $2\eta$).

**Statement.** Under matching moments and (C1)–(C3), for all $z\ge1$,

$$\bigl\|\mathcal L(Z_1\mid Z_0=z)-\mathcal L(\widetilde Z_1\mid\widetilde Z_0=z)\bigr\|_{TV}\le J(z)=\frac{\sqrt2\,\bigl(3R+2(1+h)\widetilde\sigma^2\bigr)}{\widetilde\sigma^2(h\wedge1)\sqrt{\pi\eta z}}+\frac{\bigl(5\sqrt{2\pi}+\tfrac{3\pi}2\bigr)(1+h)R+h\widetilde\sigma^2}{\widetilde\sigma^3\sqrt{2\pi h^3z}},$$

and for every $k\ge1$ and $\alpha\in(0,1)$,

$$\bigl\|\mathcal L(Z_1,\dots,Z_k\mid Z_0=z)-\mathcal L(\widetilde Z_1,\dots,\widetilde Z_k\mid\widetilde Z_0=z)\bigr\|_{TV}\le\sum_{i=0}^{k-1}J\bigl((\alpha\widetilde mh)^iz\bigr)+\frac{\widetilde\sigma^2}{(1-\alpha)^2\widetilde m^2hz}\sum_{i=0}^{k-2}(\alpha\widetilde mh)^{-i}.$$

For fixed $k$ the distance is $O(z^{-1/2})$. If $\widetilde mh>1$, choosing $\alpha\in(1/(\widetilde mh),1)$ makes the bound uniform in $k$, so the whole trajectories of the two processes are within $O(z^{-1/2})$ in total variation: large populations cannot distinguish the two density-regulation mechanisms.

## Depends on

- [Equivalence of controlled and population-size-dependent branching processes](equivalence-of-controlled-and-population-size-dependent-branching.md)

## Expansion

The one-step bound compares both one-step laws, which are sums of about $z$ independent lattice variables with equal mean and variance, with a common discretized normal law, using Berry–Esseen-type local estimates; (C3) excludes lattice periodicity and (C1) keeps the number of summands of order $z$. The $k$-step bound follows by induction: on the event that the population has not fallen below the geometric track $(\alpha\widetilde mh)^iz$, the one-step errors add up, and Chebyshev's inequality controls the probability of leaving that track.

## Sources

- Peter Braunsteins, Sophie Hautphenne and James Kerlidis, "Linking population-size-dependent and controlled branching processes", Stochastic Processes and their Applications 181 (2025), 104556, <https://doi.org/10.1016/j.spa.2024.104556>; numbering as in arXiv:2308.01150: Lemma 4.4, Proposition 4.5, Corollary 4.9, Propositions 4.10–4.11.
