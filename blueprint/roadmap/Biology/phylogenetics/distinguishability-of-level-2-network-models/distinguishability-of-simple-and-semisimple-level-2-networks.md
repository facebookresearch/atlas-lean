# Distinguishability of simple and semisimple level-2 networks

**Definitions.** For a class of network models $\{M_N\}$ with varieties $V_N$, networks $N_1,N_2$ are **distinguishable** if $V_{N_1}\cap V_{N_2}$ is a proper subvariety of both $V_{N_1}$ and $V_{N_2}$; if every pair of distinct $n$-leaf networks in the class is distinguishable, the network parameter is generically identifiable. A **simple level-$k$ network** is obtained from a level-$k$ generator by subdividing edges and attaching one leaf per subdivision vertex. A **semisimple level-2 network** is a strict level-2 network with exactly two reticulation vertices; its cut edges leaving the level-2 block partition the leaves into **branches**, and a branch (or a leaf, in the simple case) is a **reticulation branch** (reticulation leaf) when it hangs below a reticulation vertex. Write $r(N)$ for the set of reticulation leaves and $R(N)$ for the set of reticulation branches; each has one or two elements. A **cycle network** is a level-1 network with exactly one reticulation vertex.

**Theorem (level-2 versus level-1).** For the group-based network models considered:
1. For $n\ge4$, if $N_1$ is an $n$-leaf semisimple nice strict level-2 network and $N_2$ an $n$-leaf cycle network, then $V_{N_1}\not\subseteq V_{N_2}$.
2. For $n\ge5$, if $N_1$ is a simple nice strict level-2 network and $N_2$ a cycle network, then $V_{N_1}\not\subseteq V_{N_2}$; if moreover $N_1$ has two reticulation leaves and $N_2$ is an $n$-cycle network whose reticulation leaf is not a reticulation leaf of $N_1$, then $N_1,N_2$ are distinguishable.

**Theorem (pairs of simple nice level-2 networks, $n\ge5$).** Let $N_1\ne N_2$ be $n$-leaf simple nice strict level-2 networks. Call $(N_1,N_2)$ $N_1$-reticulation-conflicting if every $x\in r(N_1)$ has some $y\in r(N_2)$ with $d_{N_1}(x,y)=3$ (and symmetrically). Then $N_1,N_2$ are distinguishable in each case:
- $|r(N_1)|=|r(N_2)|=2$, $r(N_1)\ne r(N_2)$, and the pair is reticulation-conflicting in neither direction;
- $r(N_1)=\{a,b\}$, $r(N_2)=\{c\}$ with $c\notin\{a,b\}$, $d_{N_1}(x,y)\ge4$ for $x\in r(N_1)$, $y\in r(N_2)$, the pair is not $N_2$-conflicting, and $d_{N_2}(a,u),d_{N_2}(b,u)\ge3$ for the purely interior reticulation vertex $u$ of $N_2$;
- $r(N_1)=\{a\}$, $r(N_2)=\{b\}$, $a\ne b$, neither conflicting, and $d_{N_1}(b,u),d_{N_2}(a,u)\ge3$ for the purely interior reticulation vertex $u$.

The semisimple analogues hold with leaves replaced by branches, distances measured in restrictions of the networks, and the extra hypothesis that the reticulation branches of $N_1$ and $N_2$ are disjoint.

## Depends on

- [Nice phylogenetic networks](nice-phylogenetic-networks.md)

## Expansion

Distinguishability is proved by exhibiting, for each ordered pair, a phylogenetic invariant (computed in Fourier coordinates) that vanishes on one variety but not the other. The base case is a computer-algebra classification of 4-leaf nice level-2 networks: a simple nice strict level-2 network is not contained in any level-1 network variety under JC, K2P or K3P. For $n\ge5$, restricting both networks to suitable 4-leaf subsets transfers these non-containments: the conflict and distance hypotheses guarantee a 4-leaf subset on which the restrictions differ in a way detected by the base case, and invariants of restrictions pull back to invariants of the full networks.

## Sources

- M. Ardiyansyah, "Distinguishing Level-2 Phylogenetic Networks Using Phylogenetic Invariants", arXiv:2104.12479 (2021), Definitions 3.3–3.4, 4.4, 6.9 and 7.4, Proposition 3.5, Proposition 5.4, Proposition 6.8, Theorems 6.13, 6.14, 6.16, 7.1, 7.6, 7.7 and 7.9, <https://doi.org/10.48550/arXiv.2104.12479>.
