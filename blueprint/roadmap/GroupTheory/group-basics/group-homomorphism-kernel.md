# Kernel of a homomorphism from a group

Let $G$ be a group and let $M$ be a set with a multiplication and an element $1_M$ such that $1_M a = a 1_M = a$ for every $a \in M$; for example $M$ can be a group $H$. Let $\varphi\colon G \to M$ be a homomorphism: $\varphi(gh) = \varphi(g)\varphi(h)$ for all $g, h \in G$ and $\varphi(1_G) = 1_M$. When $M$ is a group the second condition follows from the first. The *kernel* of $\varphi$ is $\ker\varphi = \{g \in G : \varphi(g) = 1_M\}$. It is a subgroup of $G$: it contains $1_G$, it is closed under products, and it is closed under inverses, since $\varphi(g) = 1_M$ gives $\varphi(g^{-1}) = \varphi(g^{-1})\varphi(g) = \varphi(g^{-1}g) = \varphi(1_G) = 1_M$.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the kernel, as a subgroup, of a homomorphism from a group to a type with a multiplication and an identity element: `MonoidHom.ker`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Subgroup/Ker.lean#L231-L243.
