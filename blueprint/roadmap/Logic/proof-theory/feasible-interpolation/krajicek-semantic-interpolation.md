# Krajíček's interpolation theorem for semantic derivations

Let $N = n + s + t$, let $A_1,\dots,A_m \subseteq \{0,1\}^{n+s}$ and $B_1,\dots,B_\ell \subseteq \{0,1\}^{n+t}$, and let $\tilde A_i, \tilde B_j \subseteq \{0,1\}^N$ be their cylinders (extended arbitrarily on the last $t$, respectively the middle $s$, coordinates). For $D \subseteq \{0,1\}^N$, the *communication complexity* $CC(D)$ is the least number of bits two players, one knowing $u \in \{0,1\}^n$ and $q_u \in \{0,1\}^s$ and the other knowing $v \in \{0,1\}^n$ and $r_v \in \{0,1\}^t$, must exchange in the worst case to solve each of the tasks: decide whether $(u, q_u, r_v) \in D$; decide whether $(v, q_u, r_v) \in D$; and, if exactly one of the two tuples lies in $D$, find $i \le n$ with $u_i \ne v_i$. Suppose there is a semantic derivation $D_1,\dots,D_k = \emptyset$ from $\tilde A_1,\dots,\tilde A_m, \tilde B_1,\dots,\tilde B_\ell$ with $CC(D_i) \le t'$ for all $i \le k$. Then the sets

$$U = \{u : \exists q\; (u,q) \in \textstyle\bigcap_i A_i\}, \qquad V = \{v : \exists r\; (v,r) \in \textstyle\bigcap_j B_j\}$$

are separated by a Boolean circuit of size at most $(k + 2n)\, 2^{O(t')}$. If moreover the $A_i$ satisfy the monotonicity condition $(u,q) \in \bigcap_i A_i \wedge u \le u' \Rightarrow (u',q) \in \bigcap_i A_i$ and every $D_i$ has monotone communication complexity (with respect to $U$) at most $t'$, or symmetrically for the $B_j$ and $V$, then $U$ and $V$ are separated by a monotone circuit of size at most $(k + n)\, 2^{O(t')}$.

## Proof sketch

Holding $u \in U$ and $v \in V$ with witnesses, the players walk from $D_k = \emptyset$ towards the initial sets, keeping both mixed tuples $(u, q_u, r_v)$ and $(v, q_u, r_v)$ outside the current line: from a line derived from $X$ and $Y$ they move to $X$ if neither tuple lies in $X$, to $Y$ if both do. No initial set avoids both tuples, so they eventually reach a premise containing exactly one tuple, where they find $i$ with $u_i \ne v_i$. This is a protocol for the Karchmer–Wigderson game on $(U, V)$ with $k + 2n$ nodes, and a protocol with $K$ nodes and communication $t'$ yields a separating circuit of size $K\, 2^{O(t')}$ (monotone for a monotone protocol).

## Depends on

- [Semantic derivations](semantic-derivations.md)
- [Communication cost of a protocol](../../../TheoryOfComputation/communication-complexity/deterministic-communication-protocols/depth.md)
- [Boolean gates](../../../TheoryOfComputation/circuit-complexity/boolean-circuits/boolean-gate.md)

## Proof depends on

- [Circuits from dag-like Karchmer–Wigderson protocols](../../../TheoryOfComputation/circuit-complexity/circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/formula-depth-and-karchmer-wigderson-games/circuits-from-dag-like-protocols.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997: Definition 4.3, Theorem 2.3 and Theorem 5.1.
