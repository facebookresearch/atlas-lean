# Symplectic matrices have determinant one

Let $R$ be a commutative ring, $l$ a finite set and $J = \begin{pmatrix} 0 & -I \\ I & 0 \end{pmatrix}$, indexed by the disjoint union $l \sqcup l$. Every square matrix $A$ over $R$ indexed by $l \sqcup l$ with $A J A^{\mathsf T} = J$ has $\det A = 1$.

## Idea

The condition $AJA^{\mathsf T} = J$ says that $A$ preserves the standard symplectic form, the antisymmetric bilinear form behind Hamiltonian mechanics. Taking determinants only gives $(\det A)^2 = 1$. The sign is fixed by the Pfaffian, a polynomial square root of the determinant of an antisymmetric matrix that satisfies $\operatorname{Pf}(AJA^{\mathsf T}) = \det(A)\operatorname{Pf}(J)$; since $\operatorname{Pf}(J) = \pm 1$ is a unit, this gives $\det A = 1$ over every commutative ring. Over a field the statement says that the symplectic group lies inside the special linear group.

## Statements

- [Symplectic matrices have determinant one](symplectic-matrix-det.md)
