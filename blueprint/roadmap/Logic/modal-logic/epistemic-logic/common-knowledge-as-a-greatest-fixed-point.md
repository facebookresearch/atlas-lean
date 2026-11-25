# Common knowledge as a greatest fixed point

Let $M = (W, (R_i)_{i \in A}, V)$ be a multi-agent Kripke model with arbitrary accessibility relations, $G \subseteq A$ a group of agents, possibly empty, and $R_G = \bigcup_{i \in G} R_i$. For a set of worlds $P$, let $E_G(P) = \{w : \forall v.\, w R_G v \Rightarrow v \in P\}$ (everybody in $G$ knows $P$). The *positive-length* common-knowledge operator $C^+_G(P)$ is the set of worlds $w$ such that $v \in P$ for every $v$ reachable from $w$ by an $R_G$-path of length at least $1$, and the *zero-step* operator $C^0_G(P)$ also includes the path of length $0$. Then:

1. $C^+_G(P) = \bigcap_{k \ge 1} E_G^k(P)$, and $C^+_G(P)$ is the greatest fixed point of $X \mapsto E_G(P \cap X)$;
2. $C^0_G(P) = P \cap C^+_G(P)$ and $C^+_G(P) = E_G(C^0_G(P))$;
3. the two operators differ at the boundary: for $G = \emptyset$, $C^+_G(P) = W$ while $C^0_G(P) = P$; and a world with no $R_G$-successor belongs to $C^+_G(P)$ for every $P$, but to $C^0_G(P)$ only if it lies in $P$;
4. if $G = \{i\}$ and $R_i$ is transitive, then $C^+_G(P) = E_i(P)$; and if the union relation $R_G$ is reflexive (for instance, $G$ is nonempty and every $R_i$ with $i \in G$ is reflexive), then $C^0_G(P) = C^+_G(P)$.

No frame condition is needed for 1 and 2.

## Expansion

This page becomes ready once these prerequisites are stated:

- Zero-step common-knowledge unfolding and induction (proof prerequisite)

## Sources

- R. Fagin, J. Y. Halpern, Y. Moses and M. Y. Vardi, *Reasoning About Knowledge*, MIT Press, 1995
- J. Y. Halpern and Y. Moses, "Knowledge and common knowledge in a distributed environment", *Journal of the ACM* 37(3):549–587, 1990
