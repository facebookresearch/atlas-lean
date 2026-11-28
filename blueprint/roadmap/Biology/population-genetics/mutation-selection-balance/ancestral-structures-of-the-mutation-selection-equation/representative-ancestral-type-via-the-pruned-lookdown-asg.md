# Representative ancestral type via the pruned lookdown ASG

**Setting.** As in [the killed ASG duality](killed-ancestral-selection-graph-duality-for-the-mutation-selection-equation.md): the deterministic mutation–selection equation with selection $s \ge 0$, mutation rate $u > 0$ and mutation probabilities $\nu_0, \nu_1$, with stable equilibrium $\bar y$. In the deterministic limit there are no coalescences, so instead of a common ancestor one follows the **representative ancestral (RA) type** $J_r \in \{0,1\}$: the type of the ancestor, at backward time $r$, of a generic individual in a population with type-1 frequency $y_0$. Let $g_r(y_0) = P_{y_0}(J_r = 1)$ and $g_\infty(y_0) = \lim_{r\to\infty} g_r(y_0)$.

**Pruned lookdown ASG.** Lines occupy levels $1,\dots,L_r$. Each line branches at rate $s$, inserting the incoming branch at its level and pushing higher lines up by one. A deleterious mutation (rate $u\nu_1$ per line) on a line below the top prunes it and the lines above slide down; a beneficial mutation (rate $u\nu_0$ per line) at level $i$ removes all lines above $i$. The true ancestor is the lowest level whose line is of type 0 at time $0$, or the top line if all are of type 1, so

$$g_r(y_0) = E_1\big[y_0^{L_r}\big] = 1 - (1-y_0)\sum_{n\ge0} P_1(L_r > n)\,y_0^n.$$

**Proposition (recurrence and stationary law).**

1. If $s = 0$, $L$ is absorbed in $1$.
2. If $u < s$ and $\nu_0 = 0$, $L$ is transient: $L_r \to \infty$ a.s.
3. If $u = s$ and $\nu_0 = 0$, $L$ is null recurrent.
4. If $u > s$ or $\nu_0 > 0$, $L$ is positive recurrent and its stationary law is geometric, $L_\infty \sim \mathrm{Geom}(1-p)$ (it has the lack-of-memory property $P(L_\infty > n+k \mid L_\infty > n) = P(L_\infty > k)$), with

$$p = \frac{s}{u\nu_1}\,\bar y \ \ (\nu_1 > 0), \qquad p = \frac{s}{u+s} \ \ (\nu_1 = 0).$$

The tail probabilities $a_n = P(L_\infty > n)$ satisfy $a_n = \frac{s}{u+s}a_{n-1} + \frac{u\nu_1}{u+s}a_{n+1}$ with $a_0 = 1$, $a_n \to 0$.

**Theorem (ancestral type distribution).**

1. If $s = 0$, $g_\infty(y_0) = y_0$.
2. If $u \le s$ and $\nu_0 = 0$, $g_\infty(y_0) = 0$ for $y_0 \in [0,1)$ and $g_\infty(1) = 1$.
3. If $s > 0$ and either $u > s$ or $\nu_0 > 0$,

$$g_\infty(y_0) = \frac{(1-p)\,y_0}{1 - p\,y_0}.$$

For $s > 0$ and $y_0 \in (0,1)$, $g_\infty$ is strictly increasing in $\nu_0$. Moreover $g_\infty(y_0)$ is the probability that a piecewise-deterministic Markov process $\tilde Y$, dual to $L$ via $E[\tilde Y_t^n \mid \tilde Y_0 = y_0] = E[y_0^{L_t} \mid L_0 = n]$, is absorbed at $1$.

## Depends on

- [Killed ancestral selection graph duality for the mutation–selection equation](killed-ancestral-selection-graph-duality-for-the-mutation-selection-equation.md)

## Expansion

With a geometric stationary law, $g_\infty(y_0) = E[y_0^{L_\infty}] = \sum_{k\ge1}(1-p)p^{k-1}y_0^k$ gives the closed form in case 3. The recursion for $a_n$ is a first-step analysis of the Siegmund dual $D$ of $L$ ($P(m \le L_t \mid L_0 = n) = P(D_t \le n \mid D_0 = m)$), for which $a_n$ is the probability of absorption at $1$ from $n+1$; it is the deterministic-limit analogue of Fearnhead's recursion for the common-ancestor type in the diffusion limit. In the transient regime $u < s$, $\nu_0 = 0$, the lookdown graph grows without bound, so the representative ancestor is fit as soon as any fit individual is present at time $0$, even though the equilibrium unfit frequency is $\bar y = u/s > 0$.

## Sources

- Ellen Baake, Fernando Cordero and Sebastian Hummel, "A probabilistic view on the deterministic mutation–selection equation: dynamics, equilibria, and ancestry via individual lines of descent", *J. Math. Biol.* 77(3) (2018), 795–820. <https://doi.org/10.1007/s00285-018-1228-8>
- Preprint version (the locators in this item follow its numbering): Ellen Baake, Fernando Cordero and Sebastian Hummel, "A probabilistic view on the deterministic mutation–selection equation: dynamics, equilibria, and ancestry via individual lines of descent", arXiv:1710.04573 (2017), Section 5 (Definition 9, Propositions 11, 14, 17 and 19, Corollaries 21–22) and Section 6 (Theorem 23, Corollary 24, Theorem 25, Corollary 26), <https://doi.org/10.48550/arXiv.1710.04573>.
