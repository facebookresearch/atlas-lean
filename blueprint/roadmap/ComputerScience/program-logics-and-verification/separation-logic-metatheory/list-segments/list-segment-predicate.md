# List segment predicate

In the heap model of [separation logic](../separating-implication-and-small-axioms/separating-implication.md), with $i \mapsto a, j$ asserting that the heap consists of exactly two consecutive cells at $i$ and $i+1$ holding $a$ and $j$, the assertion $\mathrm{list}\ \alpha\ (i, j)$ states that there is a singly-linked list segment from $i$ to $j$ representing the finite sequence $\alpha$. It is defined by induction on $\alpha$:

$$\mathrm{list}\ \epsilon\ (i, j) \;=\; \mathrm{emp} \wedge i = j, \qquad \mathrm{list}\ (a \cdot \alpha)\ (i, k) \;=\; \exists j.\ (i \mapsto a, j) \ast \mathrm{list}\ \alpha\ (j, k).$$

Unfolding, $\mathrm{list}\ \alpha_1 \cdots \alpha_n\ (i_0, i_n)$ holds exactly when $\exists i_1, \dots, i_{n-1}.\ (i_0 \mapsto \alpha_1, i_1) \ast \cdots \ast (i_{n-1} \mapsto \alpha_n, i_n)$; so $i_0, \dots, i_{n-1}$ are distinct, while $i_n$ is unconstrained.

## Depends on

- [Separating implication](../separating-implication-and-small-axioms/separating-implication.md)

## Sources

- J. C. Reynolds, "Separation logic: a logic for shared mutable data structures", *Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002)*, IEEE, 2002, author copy <https://www.cs.cmu.edu/~jcr/seplogic.pdf>, Section 5.
