# Pole-shifting theorem

Let $V$ be an $n$-dimensional vector space over a field, $U$ a vector space, and $A : V \to V$, $B : U \to V$ linear maps with $\operatorname{Span} \{ A^i B u : u \in U, \ 0 \le i < n \} = V$ (the Kalman rank condition). Then for every monic polynomial $P$ of degree $n$ there is a linear map $K : V \to U$ such that $A + B K$ has characteristic polynomial $P$.

This is the pole-shifting theorem of Wonham (1967), as stated in Coron, *Control and Nonlinearity* (AMS 2007), Theorem 10.1 (over $\mathbb{R}$, for controllable systems, which by Theorem 1.16 are those satisfying the rank condition), and in Sontag, *Mathematical Control Theory* (2nd ed., 1998), Theorem 13 (over any field; this is the direction "controllable ⇒ every monic polynomial of degree $n$ is assignable" of its last sentence). The proof is Coron's: Heymann's lemma gives $f \in U$ and $C : V \to U$ such that the single-input system $\dot x = (A + BC) x + (Bf) v$ satisfies the rank condition; single-input pole placement gives a linear form $K_1$ with $\chi_{A + BC + (Bf) K_1} = P$, and $K = C + f K_1$.

## Informally uses

- [Heymann's lemma](exists-span-pow-add-comp-eq-top.md): the reduction to one input (Coron, Lemma 10.3).
- [Pole placement for single-input systems](exists-charpoly-add-smul-right-eq.md): the case $m = 1$, applied to the single-input system given by Heymann's lemma.

## Background

- [Exponential stabilisation of controllable linear systems](exists-norm-exp-add-mul-le.md): assigning a polynomial whose roots have negative real parts makes $0$ globally asymptotically stable for $\dot x = (A + BK) x$ (Coron, Corollary 10.12).
