# Uniform bounded height for self quasi-isometries of solvable Lie models

Let $S$ be a simply connected solvable real Lie group as above, unimodular for Borel Haar measure, with a proper left-invariant metric inducing its topology and admitting bounded-step chains of length at most a fixed affine function of distance. Suppose an ordered real basis triangularizes every adjoint Lie algebra endomorphism. Let $W$ be a finite-dimensional normed real vector space identified by $q$ with the Lie algebra modulo the common kernel of the diagonal characters. Assume an exponential $\exp$ with the one-parameter subgroup law and derivative $x$ at zero on $t\mapsto\exp(tx)$, and an additive height homomorphism $\pi:S\to W$ satisfying $\pi(\exp x)=q([x])$.

There is one finite subgroup $A\le\mathrm{GL}(W)$ so that for every $K\ge1,C\ge0$ there is $B\ge0$ such that each self map $F$ with $d(Fx,Fy)\le Kd(x,y)+C$, $d(x,y)\le Kd(Fx,Fy)+KC$, and $C$-dense image has a single $a_F\in A$ with $\|\pi(Fg)-\pi(F1)-a_F\pi(g)\|\le B$ for all $g$. The slope group is chosen before $K,C$ and the error bound before $F$.

## Depends on

- Coarse chain metric, real triangular adjoint action, height quotient and exponential compatibility.

## Proof depends on

- Finite slope-group construction and uniform bounded-error comparison for all quasi-isometries with the chosen constants.

## Expansion

Separate extraction of the diagonal characters, existence and finiteness of their height symmetries, and the height estimate for arbitrary self quasi-isometries. Treat a trivial height space as an allowed case.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PolycyclicRecognition.lean#L218-L234) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PolycyclicRecognition.lean).
