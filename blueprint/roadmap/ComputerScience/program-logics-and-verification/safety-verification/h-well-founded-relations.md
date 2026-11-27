# H-well-founded relations

Let $R$ be a binary relation on a set $I$. A finite sequence $\langle x_1, \dots, x_n \rangle$ in $I$ is *$R$-homogeneous* (an $R$-decreasing transitive sequence) if $x_j \mathrel{R} x_i$ for all $1 \le i < j \le n$; let $H(R)$ be the set of these sequences. $R$ is *H-well-founded* if $H(R)$ is well-founded under one-step extension in the inductive sense: every property of sequences that holds of a sequence $s \in H(R)$ whenever it holds of all the one-step extensions $\langle s, x \rangle$ of $s$ that lie in $H(R)$ holds of every sequence in $H(R)$. Classically, this is equivalent to there being no infinite sequence of elements of $H(R)$ each obtained from the previous one by appending one element, that is, no infinite sequence $x_1, x_2, \dots$ all of whose finite prefixes lie in $H(R)$; intuitionistically the inductive definition is the stronger one, and it is the one for which the [H-closure theorem](h-closure-theorem.md) has an intuitionistic proof.

Every well-founded relation is H-well-founded, since an $R$-homogeneous sequence is in particular $R$-decreasing: induction on the last element of a sequence gives induction over one-step extensions.

## Related topics

- [H-closure theorem](h-closure-theorem.md)

## Sources

- S. Berardi, P. Oliva and S. Steila, "Proving termination of programs having transition invariants of height ω", *Proceedings of the 15th Italian Conference on Theoretical Computer Science (ICTCS 2014)*, CEUR Workshop Proceedings 1231, 2014, pp. 237–240, <https://ceur-ws.org/Vol-1231/short1.pdf>, Section 3 (definition of $H(R)$ and of H-well-foundedness).
