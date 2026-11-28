# The theory of modules over a finitely controlled wild algebra is undecidable

For a finite-dimensional algebra over a countable, recursively given field that is finitely controlled wild, no algorithm decides which first-order sentences in the language of its modules hold in some module.

**Setting.** Let $k$ be a field and $R$ a finite-dimensional $k$-algebra; $\mathrm{mod}\text{-}R$ is the category of finitely generated right $R$-modules and $\mathrm{fin}\text{-}S$ the category of finite-dimensional right modules over a $k$-algebra $S$. A faithful exact functor $F:\mathrm{fin}\text{-}S\to\mathrm{mod}\text{-}R$ is a *controlled representation embedding* if there is a full subcategory $\mathcal C$ of $\mathrm{mod}\text{-}R$, closed under direct sums and direct summands, such that for all $M,N\in\mathrm{fin}\text{-}S$

$$
\mathrm{Hom}_R(FM,FN)=F\,\mathrm{Hom}_S(M,N)\oplus\mathrm{Hom}_R(FM,FN)_{\mathcal C},\qquad\mathrm{Hom}_R(FM,FN)_{\mathcal C}\subseteq\mathrm{rad}\,\mathrm{Hom}_R(FM,FN),
$$

where $\mathrm{Hom}_R(FM,FN)_{\mathcal C}$ consists of the morphisms factoring through an object of $\mathcal C$; it is *finitely controlled* if $\mathcal C$ can be taken to be $\mathrm{add}(C)$ for a single module $C$. The algebra $R$ is *finitely controlled wild* if there is a finitely controlled representation embedding $\mathrm{fin}\text{-}k\langle X,Y\rangle\to\mathrm{mod}\text{-}R$ from the finite-dimensional modules over the free algebra on two generators. The *theory of $\mathrm{Mod}\text{-}R$* is the set of first-order sentences in the language of right $R$-modules (addition, zero and a unary function symbol for each $r \in R$) true in every right $R$-module. Since $k$ is countable and recursively given and $R$ is finite-dimensional, the elements of $R$, and hence the sentences, are coded by finite data (coordinates in a fixed $k$-basis of $R$), so the decision problem is well posed; this coding is the page's own gloss, not the source's.

**Theorem (Gregory and Prest).** Let $k$ be a countable recursively given field and $R$ a finitely controlled wild $k$-algebra. Then the theory of $\mathrm{Mod}\text{-}R$ is undecidable.

When $k$ is algebraically closed, every local wild $k$-algebra and every wild $k$-algebra with square-zero radical is finitely controlled wild, so the theorem applies to them; the source leaves open whether it extends to all wild algebras.

## Depends on

- [Field](../../../Algebra/rings-and-fields/field.md)
- [Finite-dimensional vector space](../../../LinearAlgebra/bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Module over a semiring](../../../Algebra/modules/module.md)

## Proof depends on

None.

## Expansion

The proof shows that finitely controlled representation embeddings can be reversed by interpretation functors: such an embedding of $S$-modules into $R$-modules yields an interpretation of the category of $S$-modules in a definable subcategory of $R$-modules, so each sentence $\sigma$ about $S$-modules translates effectively into a sentence $\sigma'$ about $R$-modules with an $R$-module satisfying $\sigma'$ exactly when some $S$-module satisfies $\sigma$. Taking for $S$ the finite-dimensional path algebra on two vertices used in the proof of Corollary 4.7 of the source, whose theory of modules is undecidable (the source cites Prest's book, Section 17.3), there is a finitely controlled representation embedding of its modules into $R$-modules, and decidability of the theory of $R$-modules would decide which sentences hold in some $S$-module. A good expansion links the undecidability of the theory of modules over that algebra, proved by encoding the word problem for groups (Prest's book, Section 17.3), and the reversal of finitely controlled representation embeddings by interpretation functors.

## Sources

- L. Gregory and M. Prest, "Representation embeddings, interpretation functors and controlled wild algebras", *Journal of the London Mathematical Society* 94(3), pp. 747–766, 2016, doi:[10.1112/jlms/jdw055](https://doi.org/10.1112/jlms/jdw055); read in arXiv:1411.3221v2 ([arXiv](https://arxiv.org/abs/1411.3221v2)), whose numbering is used: the definitions opening Section 4 (controlled representation embeddings and controlled wild algebras), Corollary 4.7 with its proof, and the remark after it on examples.
