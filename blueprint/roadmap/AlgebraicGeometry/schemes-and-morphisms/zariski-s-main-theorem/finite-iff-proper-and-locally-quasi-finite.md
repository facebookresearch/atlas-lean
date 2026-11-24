# Finite morphisms are the proper locally quasi-finite morphisms

A morphism of schemes $f \colon X \to Y$ is finite if and only if it is proper and locally
quasi-finite. Here $f$ is locally quasi-finite if for all affine open subsets $U \subseteq Y$ and $V
\subseteq f^{-1}(U)$ and every prime ideal $\mathfrak{p}$ of $\mathcal{O}(U)$, the fibre
$\kappa(\mathfrak{p}) \otimes_{\mathcal{O}(U)} \mathcal{O}(V)$ is a finite-dimensional vector space
over $\kappa(\mathfrak{p})$. This is Mathlib's convention: unlike the Stacks Project's definition
(Tag 01TD), it does not require $f$ to be locally of finite type, so that, for instance,
$\operatorname{Spec} \mathbb{Q} \to \operatorname{Spec} \mathbb{Z}$ is locally quasi-finite in this sense. The equivalence is the same
under either convention, since a proper morphism is of finite type. For a morphism of finite type
the condition amounts to finite fibres, so a proper morphism with finite fibres is finite.

## Sources

- The Stacks Project, Lemma 37.44.1, <https://stacks.math.columbia.edu/tag/02LS>: the equivalence of
  (1), (2) and (3).
