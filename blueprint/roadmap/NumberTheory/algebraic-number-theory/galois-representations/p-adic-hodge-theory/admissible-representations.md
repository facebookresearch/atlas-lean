# Admissible representations for a regular ring of periods

Let $G$ be a topological group, $F$ a topological field and $B$ an $F$-algebra with a continuous action of
$G$, and let $E = B^G$. The ring $B$ is **$(F, G)$-regular** if (i) $B$ is a domain, (ii)
$B^G = (\operatorname{Frac} B)^G$, and (iii) every nonzero $b \in B$ such that the line $Fb$ is stable under $G$ is
invertible in $B$; then $E$ is a field. For an $F$-representation $V$ of $G$ (a finite-dimensional $F$-vector
space with a continuous linear action) put $D_B(V) = (B \otimes_F V)^G$, an $E$-vector space, and let
$\alpha_V \colon B \otimes_E D_B(V) \to B \otimes_F V$ be the natural map. $V$ is **$B$-admissible** if
$\alpha_V$ is an isomorphism.

If $B$ is $(F, G)$-regular, then for every $F$-representation $V$ the map $\alpha_V$ is injective and
$\dim_E D_B(V) \le \dim_F V$, with equality exactly when $V$ is $B$-admissible. The $B$-admissible
representations form a full subcategory of the representations of $G$ closed under subobjects, quotients,
direct sums, tensor products and duals, and on it $D_B$ is an exact faithful functor with
$D_B(V_1 \otimes V_2) \cong D_B(V_1) \otimes_E D_B(V_2)$ and $D_B(V^*) \cong D_B(V)^*$.

## Depends on

This node has no prerequisites.

## Proof depends on

This node has no prerequisites.

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §3.1, Definition 3.9 ($(F, G)$-regular rings) and Remark 3.10, Definitions 3.11–3.13 (sub-Tannakian categories,
  $B$-admissible representations), Theorem 3.14 (1)–(2) (injectivity of $\alpha_V$, the dimension criterion, and
  the exact faithful tensor functor $D_B$).
