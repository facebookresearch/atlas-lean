# The automorphism spelled by a word

Let $F_n$ be the free group on $n$ generators and let
$g_0, \dots, g_{k-1}$ be automorphisms of $F_n$. A word $w = ((i_1, b_1), \dots, (i_r, b_r))$ is a
finite list of letters $(i, b)$ with $i \in \mathbb{N}$ and $b$ a boolean. The automorphism
spelled by $w$ over $(g_i)$ is the product $a_1 a_2 \cdots a_r$ in $\operatorname{Aut}(F_n)$,
whose group operation is composition, where for $i_j < k$ the factor $a_j$ is $g_{i_j}$ if $b_j$ is
true and $g_{i_j}^{-1}$ if $b_j$ is false, and for $i_j \ge k$ the factor $a_j$ is the identity.
The empty word spells the identity.
