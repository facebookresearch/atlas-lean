---
article_id: af_c1b8fd4718185115f01a2d80
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: RealNumbers.field_axioms
---

# Definition (Field) (Real Numbers, Ordered Sets & Fields)

A set $F$ is a field if it has two operations: addition $(+)$ and multiplication $(\cdot)$ with the following properties. A1) If $x, y \in F$ then $x + y \in F$. A2) (Commutativity) $\forall x, y \in F$, $x + y = y + x$. A3) (Associativity) $\forall x, y, z \in F$, $(x + y) + z = x + (y + z)$. A4) $\exists$ an element $0 \in F$ such that $0 + x = x = x + 0$. A5) $\forall x \in F$, $\exists y \in F$ such that $x + y = 0$. We denote $y = -x$. M1) If $x, y \in F$, then $x \cdot y \in F$. M2) (Commutativity) $\forall x, y \in F$, $x \cdot y = y \cdot x$. M3) (Associativity) $\forall x, y, z \in F$, $(x \cdot y) \cdot z = x \cdot (y \cdot z)$. M4) $\exists 1 \in F$ such that $1 \cdot x = x = x \cdot 1$ for all $x \in F$. M5) $\forall x \in F \setminus \{0\}$, $\exists x^{-1}$ such that $x \cdot x^{-1} = 1$. D) (Distributivity) $\forall x, y, z \in F$, $(x + y)z = xz + yz$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.100A Real Analysis (Fall 2020), Real Numbers, Ordered Sets & Fields](../../../../../sources/v1/RealAnalysis.md)
