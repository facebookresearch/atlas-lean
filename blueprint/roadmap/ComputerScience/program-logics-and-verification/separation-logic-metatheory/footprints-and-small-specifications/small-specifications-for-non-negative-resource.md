# Small specifications for non-negative resource

In a separation algebra where no non-unit element has an inverse, every local function either has the specification on its footprints as a complete specification whose domain is contained in every complete domain, or has no complete specification with an inclusion-minimal domain at all. Lookup over fractional heaps gives the second case.

A separation algebra $(\Sigma, \bullet, u)$ has *negativity* if some $\sigma \neq u$ has an inverse, $\sigma \bullet \sigma' = u$ for some $\sigma'$, and is *non-negative* otherwise. Every algebra with negativity is non-well-founded. If $\Sigma$ is non-negative, then for every local function $f$ on $\Sigma$, with [footprints](footprints-of-local-functions.md) $F(f)$:

1. every basis of $f$ that contains a non-footprint $\mu$ remains a basis after removing $\mu$;
2. hence either $F(f)$ is a basis of $f$, and then it is contained in every basis, or $f$ has no inclusion-minimal basis;
3. correspondingly, either $\varphi_{F(f),f} = \{(\{\sigma\}, f(\sigma)) : F_f(\sigma)\}$ is a small [complete specification](complete-specifications.md) of $f$ whose domain $F(f)$ is contained in the domain of every complete specification of $f$, or no complete specification of $f$ is small, that is, every complete specification has a complete specification with a strictly smaller domain.

## Depends on

- [Complete specifications of local functions](complete-specifications.md)
- [Footprints of local functions](footprints-of-local-functions.md)

## Proof depends on

- [Complete specifications of local functions](complete-specifications.md)
- [Footprints are exactly the essential states of complete specifications](essentiality-of-footprints.md)
- [Footprints of local functions](footprints-of-local-functions.md)
- [Precise predicates distribute separating conjunction over intersections](../abstract-separation-logic/precise-predicates-distribute-over-meets.md)

## Expansion

Examples from the source. For heaps with fractional permissions, which are non-negative and not well-founded, the mutation of a cell has a small specification whose precondition is the cell with permission $1$; lookup is safe with any positive permission and is completely specified by the preconditions $\ell \overset{z}{\mapsto} v$ for $0 < z \le 1$, but also by those with $0 < z \le 1/2$, and every such restriction can be shrunk further, so lookup has no complete specification with an inclusion-minimal domain. In the integers $(\mathbb{Z}, +, 0)$, which have negativity, $f(n) = \{n + c\}$ is local and has no footprints, yet each $\{(\{n\}, \{n + c\})\}$, for any $n \in \mathbb{Z}$, is a small specification made of a non-footprint; these minimal domains are pairwise incomparable, so none is least.

The proof shows that a basis $A$ containing a non-footprint $\mu$ remains a basis without $\mu$. For states $\sigma$ with $\mu \not\preceq \sigma$ the meets defining $L_{A,f}(\sigma)$ and $L_{A \setminus \{\mu\},f}(\sigma)$ coincide. For $\mu \preceq \sigma$ it suffices that the term $\{\sigma - \mu\} \ast f(\mu)$ lies above the meet over $A \setminus \{\mu\}$: expand $f(\mu) = L_f(\mu)$, use non-negativity to see that $\sigma' \prec \mu$ implies $\mu \not\preceq \sigma'$, so the first case applies to each such $\sigma'$, and distribute singletons over meets by precision. Since every basis contains $F(f)$ by essentiality, if $F(f)$ is not a basis then every basis contains a removable non-footprint, so no basis is inclusion-minimal. The source states the conclusion as the absence of a smallest basis; the proof gives the inclusion-minimal form stated here. Domains of complete specifications are bases, because a complete specification and its canonicalization have the same domain and a canonical complete specification is $\varphi_{D,f}$ for its domain $D$, which transfers the dichotomy to specifications. The integer example shows that non-negativity cannot be dropped.

## Sources

- M. Raza and P. Gardner, "Footprints in local reasoning", *Logical Methods in Computer Science* 5(2:4), 2009, <https://doi.org/10.2168/LMCS-5(2:4)2009>, arXiv:0903.1032v2 <https://arxiv.org/abs/0903.1032v2>, Section 3, Definition 3.6 and Corollary 3.5; Section 5.1, Lemma 5.3 and the remark after it; Section 5.3, Definition 5.7, Theorem 5.8 and its proof, Corollary 5.9, Examples 5.10 and 5.11 (numbers from arXiv:0903.1032v2).
