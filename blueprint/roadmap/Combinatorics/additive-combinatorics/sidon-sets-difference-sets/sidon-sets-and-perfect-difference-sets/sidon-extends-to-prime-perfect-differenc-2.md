# Erdős Problem 707 is false

It is not the case that every finite Sidon set
$A \subseteq \mathbb{N}$ is contained in a perfect difference set modulo $p^2 + p + 1$ for some
prime $p$: there is a finite Sidon set $A \subseteq \mathbb{N}$ such that for every prime $p$, no
set $B \subseteq \mathbb{N}$ with $A \subseteq B$ is a perfect difference set modulo
$p^2 + p + 1$. Here $A$ is Sidon when $w + x = y + z$ with $w, x, y, z \in A$ forces
$\{w, x\} = \{y, z\}$, and $B$ is a perfect difference set modulo $v$ when every nonzero residue
$r$ modulo $v$ satisfies $r \equiv a - b \pmod{v}$ for exactly one ordered pair $(a, b)$ of
elements of $B$.

Alexeev and Mixon proved that the Sidon set $\{1, 2, 4, 8\}$ is such a set (their proof is
formalized in Lean); erdosproblems.com/707 lists the problem as disproved.

## Sources

- T. F. Bloom, Erdős Problems, Problem #707, https://www.erdosproblems.com/707 (status DISPROVED (LEAN)); resolution: B. Alexeev and D. G. Mixon, Forbidden Sidon subsets of perfect difference sets, featuring a human-assisted proof, arXiv:2510.19804 (2025); M. Hall, Jr., Cyclic projective planes, Duke Math. J. 14 (1947), 1079-1090, abstract of arXiv:2510.19804: {1, 2, 4, 8, 13} is a finite Sidon set contained in no finite perfect difference set; erdosproblems.com/707: {1, 2, 4, 8} cannot be extended to a perfect difference set modulo p² + p + 1 for any prime p, and Hall's {1, 3, 9, 10, 13} cannot be extended to any perfect difference set, https://arxiv.org/abs/2510.19804.
