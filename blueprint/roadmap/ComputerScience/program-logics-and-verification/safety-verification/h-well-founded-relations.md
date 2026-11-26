# H-well-founded relations

Let $R$ be a binary relation on a set $I$. A finite sequence $\langle x_1, \dots, x_n \rangle$ in $I$ is *$R$-homogeneous* (an $R$-decreasing transitive sequence) if $x_j \mathrel{R} x_i$ for all $1 \le i < j \le n$; let $H(R)$ be the set of these sequences. $R$ is *H-well-founded* if $H(R)$ is well-founded under one-step extension, that is, there is no infinite sequence of elements of $H(R)$ each obtained from the previous one by appending one element; equivalently, there is no infinite sequence $x_1, x_2, \dots$ all of whose finite prefixes lie in $H(R)$.

Every well-founded relation is H-well-founded, since an $R$-homogeneous sequence is in particular $R$-decreasing.

## Sources

- S. Berardi, P. Oliva and S. Steila, "Proving termination of programs having transition invariants of height ω", *Proceedings of the 15th Italian Conference on Theoretical Computer Science (ICTCS 2014)*, CEUR Workshop Proceedings 1231, 2014, pp. 237–240, <https://ceur-ws.org/Vol-1231/short1.pdf>, Section 3 (definition of $H(R)$ and of H-well-foundedness).
