# Exact pair closures for SIR epidemics on triplets and trees

Consider a stochastic SIR epidemic on a network: each node is $S$, $I$ or $R$; an infected node has an infectious period of random duration $T$ (i.i.d. across nodes) during which it contacts each neighbour at the points of a Poisson process of rate $\tau$, infecting the neighbour if susceptible, after which it is permanently removed. For a connected triple of nodes $(1,2,3)$ let $p(ABC)$ be the exact probability of the joint state $(A,B,C)$ at time $t$, and $p_{ij}$, $p_i$ the exact pair and single-node marginals. **Pair (moment) closures** reconstruct triple probabilities from these marginals:

On an **open triplet** (edges $\{1,2\}, \{2,3\}$, centre node $2$), the unclustered closure is

$$p_o(ABC) = \frac{p_{12}(AB)\,p_{23}(BC)}{p_2(B)},$$

which is also the maximum-entropy distribution with those marginals. On a **closed triangle** one uses the Kirkwood closure $p_\kappa(ABC) = \dfrac{p_{12}(AB)\,p_{23}(BC)\,p_{13}(AC)}{p_1(A)\,p_2(B)\,p_3(C)}$, the maximum-entropy closure $p_\mu$ (of product form $q_{12}(AB)q_{23}(BC)q_{31}(CA)$, computable by iterative scaling), and a one-step iterative-scaling closure $p_\rho$.

A closure is **exact** for a given initial state and target state if it equals the true probability for all $t \ge 0$.

**Theorem (trees, any infection model with independent escapes).** For any connected triplet $(i,j,k)$ in any tree-like network, any model in which a susceptible escapes infection independently from each infected neighbour and infected nodes never return to susceptibility, and any deterministic initial condition $x^0$,

$$p_o(ISS) = p(ISS) \qquad\text{and}\qquad p_o(ISI) = p(ISI) \qquad \text{for all } t \ge 0$$

(with $I$ replaced by $E$ for Reed–Frost-type models). In particular this holds for the SIR model on an open triplet started from $(ISS)$ or $(ISI)$: the states that drive new infections are closed exactly, whatever the infectious-period distribution.

**Proposition (constant infectious period).** If $T$ is a.s. constant, then on an open triplet $p_o(ABC) = p(ABC)$ for all $A,B,C \in \{S,I,R\}$, all $t \ge 0$ and all initial conditions; and on a closed triangle all three closures are exact, $p_\kappa = p_\rho = p_\mu = p$.

In contrast, for Markovian (exponential) infectious periods the closures are not exact in general, so the error of pair approximations comes from the memory of the infectious period interacting with the network structure, not from clustering alone.

## Expansion

On a tree, conditional on the state of the centre node's history, the infection processes on its two branches are independent as long as the centre is susceptible: each neighbour's transmission to the centre is an independent escape event, and nothing can pass between the leaves except through the centre. This gives conditional independence of the leaves given the centre being $S$, which is exactly the factorization $p(ASC) = p(AS)p(SC)/p(S)$. With constant infectious periods the timing of removal is a deterministic function of infection time, so the joint state of a pair is determined by infection times; the resulting distributions factorize along edges for every state, and on the triangle the surviving dependencies are of pairwise product form, which all three closures reproduce. Explicit computation of the Markovian three-node chains exhibits nonzero errors.

## Sources

- Lorenzo Pellis, Thomas House, Matt J. Keeling, "Exact and approximate moment closures for non-Markovian network epidemics", arXiv (2015). Section 2 (labelled networks, SIR, SEIR and Reed–Frost models, moment closures), Section 3 (unclustered, Kirkwood, maximum-entropy closures and iterative scaling), Sections 4–5 (Propositions 1–3), Theorem 1. <https://doi.org/10.48550/arXiv.1505.03354>. Published version: Journal of Theoretical Biology 382 (2015), 160–177, <https://doi.org/10.1016/j.jtbi.2015.04.039>; locators above refer to the arXiv version.
