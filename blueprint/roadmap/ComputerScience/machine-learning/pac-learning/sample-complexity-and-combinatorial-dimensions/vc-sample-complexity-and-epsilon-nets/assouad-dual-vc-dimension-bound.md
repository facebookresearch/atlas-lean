# Assouad's dual VC dimension bound

For a class $C$ of functions $X \to \{0,1\}$, the dual class is the class of functions on $C$ given by the evaluations $c \mapsto c(x)$, one for each $x \in X$. If every finite set shattered by $C$ has at most $d$ points, then every finite subfamily of $C$ shattered by the dual class has at most $2^{d+1} - 1$ members; that is, the dual VC dimension satisfies $d^* \le 2^{d+1} - 1$. Moreover, for maps $\varphi : Y \to X$, if $\{g \circ \varphi : g \in G\}$ shatters a set $W$ then $\varphi$ is injective on $W$ and $G$ shatters $\varphi(W)$.

## Proof sketch

If the dual class shatters $2^{k}$ concepts indexed by $\{0,1\}^k$, choose for each coordinate $j$ a witness point $x_j$ whose evaluation selects exactly the concepts whose index has $j$-th bit $1$; then the $k$ points $x_1, \dots, x_k$ are shattered by $C$ (the bit-coding argument), so $k \le d$ and the shattered family has fewer than $2^{d+1}$ members.

## Depends on

- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Sources

- P. Assouad, "Densite et dimension", Annales de l'Institut Fourier, 1983.
- S. Moran and A. Yehudayoff, "Sample Compression Schemes for VC Classes", Journal of the ACM, 2016.
