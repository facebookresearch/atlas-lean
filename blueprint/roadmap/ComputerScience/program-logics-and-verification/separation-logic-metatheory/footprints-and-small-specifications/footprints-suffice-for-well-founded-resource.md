# Footprints suffice for well-founded resource

If the strict substate relation of a separation algebra is well-founded, the footprints of every local function form a basis for it, so the function has a small specification whose domain is exactly its set of footprints, and that domain is contained in the domain of every complete specification.

Let $\Sigma$ be a separation algebra in which $\prec$ is well-founded, that is, there is no infinite chain $\sigma_1 \succ \sigma_2 \succ \cdots$. Then for every local function $f$ on $\Sigma$, with [footprints](footprints-of-local-functions.md) $F(f)$,

$$f = L_{F(f), f},$$

and $\varphi_{F(f),f} = \{(\{\sigma\}, f(\sigma)) : F_f(\sigma)\}$ is a small [complete specification](complete-specifications.md) of $f$; since every footprint lies in the domain of every complete specification, its domain $F(f)$ is the least domain of a complete specification of $f$.

## Depends on

- [Complete specifications of local functions](complete-specifications.md)
- [Footprints of local functions](footprints-of-local-functions.md)

## Proof depends on

- [Well-founded induction](../../../../Order/ordered-sets/well-founded-induction.md)
- [Footprints are exactly the essential states of complete specifications](essentiality-of-footprints.md)
- [Footprints of local functions](footprints-of-local-functions.md)
- [Precise predicates distribute separating conjunction over intersections](../abstract-separation-logic/precise-predicates-distribute-over-meets.md)

## Expansion

Ordinary finite heaps with disjoint union are well-founded: in the plain heap model disposal of $l$ has the small specification $\{(\{l \mapsto v : v \in \mathit{Val}\}, \{u_H\})\}$, a non-canonical form of $\{(\{l \mapsto v\}, \{u_H\}) : v \in \mathit{Val}\}$. Heaps with fractional permissions are not well-founded, since a permission can be halved indefinitely. Induct along $\prec$, assuming $f(\sigma') = L_{F(f),f}(\sigma')$ for all $\sigma' \prec \sigma$. If $\sigma$ is a footprint, the term $\{u\} \ast f(\sigma)$ occurs in the meet defining $L_{F(f),f}(\sigma)$, so $L_{F(f),f}(\sigma) \sqsubseteq f(\sigma)$, and locality gives the reverse. Otherwise $f(\sigma) = L_f(\sigma)$; substituting the hypothesis for each $f(\sigma')$ and distributing $\{\sigma - \sigma'\} \ast (\cdot)$ over the inner meets, which is allowed because singletons are precise and $\{\sigma\} \ast \top = \top$ covers empty meets, rewrites $L_f(\sigma)$ as the meet over footprints $\sigma'' \prec \sigma$, which equals $L_{F(f),f}(\sigma)$ because $\sigma$ itself is not a footprint. The basis characterization of completeness then makes $\varphi_{F(f),f}$ complete, and essentiality makes its domain least.

## Sources

- M. Raza and P. Gardner, "Footprints in local reasoning", *Logical Methods in Computer Science* 5(2:4), 2009, <https://doi.org/10.2168/LMCS-5(2:4)2009>, arXiv:0903.1032v2 <https://arxiv.org/abs/0903.1032v2>, Section 5.2, Theorem 5.5 and its proof, Corollary 5.6 and the remarks after it (numbers from arXiv:0903.1032v2).
