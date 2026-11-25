# Hom detects exact sequences ending in a surjection

Let $R$ be a commutative ring and let $\varphi : M \to N$ and $\psi : N \to P$ be linear maps of $R$-modules. Then $\operatorname{im} \varphi = \ker \psi$ and $\psi$ is surjective if and only if, for every $R$-module $D$ (in the same universe as $N$ and $P$), the map $\operatorname{Hom}_R(P, D) \to \operatorname{Hom}_R(N, D)$, $g \mapsto g \circ \psi$, is injective with image the kernel of $\operatorname{Hom}_R(N, D) \to \operatorname{Hom}_R(M, D)$, $h \mapsto h \circ \varphi$.

## Idea

The functor $\operatorname{Hom}_R(-, D)$ turns a right exact sequence $M \to N \to P \to 0$ into a left exact sequence $0 \to \operatorname{Hom}(P, D) \to \operatorname{Hom}(N, D) \to \operatorname{Hom}(M, D)$: maps out of $P$ are the maps out of $N$ that vanish on the image of $M$. The converse says that testing against all modules $D$ is enough to recover exactness. For the converse, take $D = N/\operatorname{im}\varphi$ and the quotient map, which kills $\operatorname{im}\varphi$ and so factors through $\psi$; then $D = P/\operatorname{im}\psi$ detects surjectivity. This is the module-theoretic form of the fact that a cokernel is determined by its universal property.

## Statements

- [Hom detects exact sequences ending in a surjection](exact-and-surjective-iff-forall-lcomp.md)
