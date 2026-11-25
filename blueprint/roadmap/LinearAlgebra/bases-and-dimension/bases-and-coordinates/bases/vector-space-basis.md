# Basis of a vector space

Let $V$ be a vector space over $\mathbb F$, where $\mathbb F$ is $\mathbb R$ or $\mathbb C$. In the finite-list
convention, a basis of $V$ (a finite ordered basis) is a list $v_1, \dots, v_n$ of vectors of $V$, of finite length
$n \ge 0$, that is linearly independent and spans $V$:

- it is linearly independent when the only scalars $a_1, \dots, a_n \in \mathbb F$ with
  $a_1 v_1 + \dots + a_n v_n = 0$ are $a_1 = \dots = a_n = 0$, the empty list being linearly independent;
- it spans $V$ when every vector of $V$ is a linear combination $a_1 v_1 + \dots + a_n v_n$ with
  $a_1, \dots, a_n \in \mathbb F$, the span of the empty list being $\{0\}$.

Only a space spanned by finitely many vectors has a basis in this sense.

## Depends on

- [Linearly independent family](linear-independent.md)

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 2.26, with 2.4 and 2.15 (version read: the open-access PDF dated 4 November 2026).
