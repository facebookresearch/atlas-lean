# Mutation limits of multi-population replicator dynamics

**Setting.** Populations $i\in I$ each have pure strategies $h\le n_i$; the state space is the product of simplices $\Delta=\prod_i\Delta_{n_i}$ and $f\in C^1(U\supset\Delta,\mathbb{R}^S)$ gives payoffs $f_{ih}(x)$ with population averages $\bar f_i(x)=\sum_h x_{ih}f_{ih}(x)$. The replicator dynamics (RD) and the replicator–mutator dynamics (RMD) with mutation rate $M>0$ toward a reference state $c\in\operatorname{int}\Delta$ are

$$\dot x_{ih}=x_{ih}\bigl(f_{ih}(x)-\bar f_i(x)\bigr),\qquad \dot x_{ih}=x_{ih}\bigl(f_{ih}(x)-\bar f_i(x)\bigr)+M\,(c_{ih}-x_{ih}).$$

A *mutation equilibrium* for $M$ is a rest point $x^M$ of the RMD.

**Definition.** A connected compact set $X\subseteq\Delta$ is a *mutation limit* if for **every** $c\in\operatorname{int}\Delta$ there is a sequence of mutation equilibria $x^{M}$, $M\to0$, converging to a point of $X$, and no proper connected compact subset of $X$ has this property. It is *attracting* if, for every $c$ and every such sequence converging into $X$, the $x^M$ are asymptotically stable for all sufficiently small $M$.

**Results.**
1. For every $M>0$ and $c$ the RMD has an interior rest point; every mutation equilibrium is an $M$-equilibrium of the game ($f_{ih}(x^M)-\bar f_i(x^M)<M$), so every accumulation point as $M\to0$ is a Nash equilibrium.
2. There is $\underline M\ge0$ such that for $M>\underline M$ the mutation equilibrium is unique, asymptotically stable, and depends $C^1$ on $M$, tending to $c$ as $M\to\infty$.
3. Every game has a mutation limit; if the set of Nash equilibria is finite, every mutation limit is a point and at least one exists.
4. Every regular Nash equilibrium (reduced Jacobian of RD of full rank) is a mutation limit point; every strict Nash equilibrium is an attracting mutation limit point.
5. If $x^*$ is an attracting mutation limit point, every eigenvalue of the reduced Jacobian of RD at $x^*$ has nonpositive real part.

In the multi-population RD no interior equilibrium is asymptotically stable, while mutation equilibria are asymptotically stable for large $M$; the notion separates Nash equilibria by whether vanishing mutation selects and stabilizes them. Attracting mutation limits do not exist in every game, and characterizing when they exist is open.

## Expansion

At a rest point of RMD, $x_{ih}(f_{ih}-\bar f_i)=-M(c_{ih}-x_{ih})$, which bounds the payoff advantage of any strategy by $M$; hence limits are Nash equilibria. Existence of interior rest points follows from a Brouwer fixed-point argument on the interior. For large $M$ the linear mutation term dominates and makes the vector field a contraction, so a unique branch $M\mapsto x^M$ exists; following this branch down by continuation, together with compactness of $\Delta$, yields a limit set independent of $c$. At a regular equilibrium the implicit function theorem continues the rest point into $M>0$ for every direction $c$; at a strict equilibrium the Jacobian is strictly stable, and stability persists under small perturbation.

## Sources

- J. Bauer, M. Broom, E. Alonso, "The Stabilisation of Equilibria in Evolutionary Game Dynamics through Mutation: Mutation Limits in Evolutionary Games", arXiv:1905.07839 (2019), Section 2 (RD, Propositions 2.2–2.8), Section 3 (RMD, Definitions 3.1–3.2, Lemmas 3.3, 3.5, 3.8–3.9, Corollary 3.6, Proposition 3.10), Section 4 (Definitions 4.1, 4.5, 4.7, Proposition 4.3, Corollary 4.4, Lemmas 4.6, 4.8, 4.11), numbering of v1 and v2, <https://doi.org/10.48550/arXiv.1905.07839>.
