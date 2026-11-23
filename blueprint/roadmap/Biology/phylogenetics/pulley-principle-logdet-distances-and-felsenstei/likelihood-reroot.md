# Pulley principle, rerooting

Let $(P_t)$ be a [reversible semigroup](is-reversible-semigroup.md) for $\pi$, let $A, B, C$ be trees and $s_1, s_2, a, b, u_1, u_2$ real with $u_1 + u_2 = a$. Then the [site likelihood](../felsenstein-s-pruning-algorithm/likelihood.md) of the tree whose root has children $x$ (on $P_{s_1}$) and $C$ (on $P_{s_2}$), where $x$ has children $A$ (on $P_a$) and $B$ (on $P_b$), equals that of the tree whose root has children $A$ (on $P_{u_1}$) and $y$ (on $P_{u_2}$), where $y$ has children $B$ (on $P_b$) and $C$ (on $P_{s_1 + s_2}$): moving the root onto an adjacent edge leaves the likelihood unchanged (Felsenstein 1981).

## Sources

- J. Felsenstein, *Evolutionary trees from DNA sequences: a maximum likelihood approach*, J. Mol. Evol. 17 (1981), 368–376.
