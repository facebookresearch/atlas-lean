# Canonical anticommutation relations

The fermionic creation and annihilation operators on a finite Fock space satisfy the canonical anticommutation relations, the algebraic form of the Pauli exclusion principle.

On $\mathcal F_M$, for all $i,j\in\{1,\dots,M\}$, with $\{A,B\}=AB+BA$,

$$
\{a_i,a_j^\dagger\}=\delta_{ij}\,\mathbf 1,\qquad \{a_i,a_j\}=0,\qquad \{a_i^\dagger,a_j^\dagger\}=0 .
$$

In particular $(a_j^\dagger)^2=0$, and $\hat n_j=a_j^\dagger a_j$ is an orthogonal projection.

## Context

Undergraduate/graduate. Every fermion-to-qubit encoding must reproduce these relations. They are the complex adjoint occupation-basis representation of the canonical relations; the abstract relation $\iota(v)\iota(w)+\iota(w)\iota(v)=2Q(v,w)$ of a Clifford algebra (Mathlib `CliffordAlgebra.ι_mul_ι_add_swap`) is a related algebraic counterpart, not a substitute.

## Depends on

- [Fermionic creation and annihilation operators](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/fermionic-creation-and-annihilation-operators.md)

## Proof depends on

None.

## Expansion

Check on basis states. For $i=j$, exactly one of $a_ia_i^\dagger$ and $a_i^\dagger a_i$ returns $|n\rangle$ (sign squared) and the other gives zero, so $\hat n_i+(\mathbf 1-\hat n_i)=\mathbf 1$. For $i<j$ the two orders either both vanish or produce the same basis state, and acting first at $i$ changes the parity count seen at $j$ by one, so the two signs differ and the terms cancel.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §V.B (pp. 28–30). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
