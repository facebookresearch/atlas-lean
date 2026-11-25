# Lower nodes of a shadow Markoff tree

Fix $v \in \mathbb{Z}^3$ and let $r$ be the
initial triple with shadow part $v$, viewed as a state (a pair of a classical part and a shadow
part, both in $\mathbb{Q}^3$, with coordinates indexed by the positions $0, 1, 2$). The lower
nodes of the shadow Markoff tree of $v$ are pairs $(s, l)$ of a state $s$ and a position $l$, the
position mutated last. They are defined inductively: the state obtained from $r$ by the shadow
Markoff mutation at position $0$ and then at position $1$, tagged with $l = 1$, is a lower node;
and if $(s, l)$ is a lower node and $i \ne l$, then the mutation of $s$ at position $i$, tagged
with $i$, is a lower node. Nothing else is a lower node.

The first lower node has classical part $(2, 5, 1)$, the paper's $(1, 2, 5)$; the lower nodes
are the nodes of the tree below the paper's $(1, 1, 2)$.

## Sources

- Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer Sequences 27 (2024), Article 24.8.3, Section 2 (the classical Markoff tree: "The initial triple `(1,1,1)` is the root of the tree. It is followed by `(1,1,2)` and `(1,2,5)`. After that, any mutation is allowed.") and Section 4.
