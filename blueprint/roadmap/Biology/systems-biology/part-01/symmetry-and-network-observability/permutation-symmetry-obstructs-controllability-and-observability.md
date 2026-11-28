# Permutation symmetry obstructs controllability and observability

**Setting.** A linear (or linearized) network model with state $x \in \mathbb{R}^n$, input $u \in \mathbb{R}^p$ and measurement $y \in \mathbb{R}^q$:

$$\dot x = A x + B u, \qquad y = C x .$$

It is controllable iff the reachable subspace $\mathcal{R} = \operatorname{span}\{ A^k B : k = 0, \dots, n-1 \}$ equals $\mathbb{R}^n$, and observable iff the unobservable subspace $\mathcal{U} = \bigcap_{k=0}^{n-1} \ker (C A^k)$ is $\{0\}$ (Kalman rank conditions). A **symmetry** is a permutation matrix $P \ne I$ of the nodes (orthogonal, $P^\top = P^{-1}$) with

$$P A = A P .$$

**Theorem.**
1. If $P B = B$ (the input enters a set of nodes that $P$ maps to itself with equal gains), then $\mathcal{R} \subseteq \operatorname{Fix}(P) = \{ x : Px = x \}$, a proper subspace; the system is not controllable.
2. If $C P = C$ (the measured output is unchanged when the symmetric nodes are permuted), then $\{0\} \neq \operatorname{range}(P - I) \subseteq \mathcal{U}$; the system is not observable.

More generally, if $G$ is a group of such symmetries, the state space decomposes into isotypic components of the irreducible representations of $G$; each component is $A$-invariant, and in a symmetry-adapted orthonormal basis $\alpha$ the system takes block form $\hat A = \alpha^\dagger A \alpha = \operatorname{diag}(A_1, A_2, \dots)$, so any block whose rows of $\hat B = \alpha^\dagger B$ vanish is uncontrollable and any block whose columns of $\hat C = C\alpha$ vanish is unobservable.

## Depends on

- [Controllability of a linear control system](../../../../Analysis/control-theory/controllability-of-linear-systems/is-controllable-on.md)
- [Kalman rank condition](../../../../Analysis/control-theory/controllability-of-linear-systems/is-controllable-on-iff-kalman.md)

## Expansion

From $PA = AP$ and $PB = B$ we get $P A^k B = A^k P B = A^k B$ for all $k$, so every column of the controllability matrix is fixed by $P$. Since $P \ne I$, $\operatorname{Fix}(P)$ is proper. For observability, $\operatorname{range}(P - I)$ is nonzero and $A$-invariant because $A(P - I) = (P - I)A$, and $C(P - I) = 0$; hence $C A^k (P - I) = C (P - I) A^k = 0$ for all $k$, so that subspace lies in $\mathcal{U}$. For example, two identical neurons coupled identically to a third, with only the third measured, have an antisymmetric mode $x_1 - x_2$ that the measurement cannot see. The block form is built from the projection-type generating matrices $G^{(p)}_i = \sum_{R \in G} D^{(p)}(R)^\ast_{ii} D(R)$, whose independent columns span the component of irreducible representation $p$; the multiplicity of $p$ is $a_p = \tfrac{1}{|G|}\sum_R \chi^{(p)}(R)^\ast \chi(R)$. For nonlinear networks such as coupled FitzHugh–Nagumo motifs, the same symmetry-induced degeneracy appears in the rank of differential-embedding (Lie-derivative) observability and Lie-bracket controllability matrices: motifs with reflection symmetries ($S_3$, $S_2$) lose observability or controllability from symmetric node choices, whereas motifs whose only symmetries are rotations ($C_3$) remain observable and controllable from every single node, since measuring one node breaks the cyclic symmetry without leaving an invariant output.

## Sources

- A. J. Whalen, S. N. Brennan, T. D. Sauer and S. J. Schiff, "Observability and controllability of nonlinear networks: the role of symmetry", Physical Review X 5 (2015), 011005, Sections II and V (Eqs. (19)–(29)), <https://doi.org/10.1103/PhysRevX.5.011005>, PMCID: PMC6234006.
- H. Rubin and H. E. Meadows, "Controllability and observability in linear time-variable networks with arbitrary symmetry groups", Bell System Technical Journal 51 (1972), 507–542.
