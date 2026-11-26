# Isogeny of abelian schemes

Let $A$ and $B$ be abelian schemes over a scheme $S$. A
morphism $f : A \to B$ over $S$ is an isogeny if it is a homomorphism of group schemes and the
underlying morphism of schemes is finite, flat and surjective. Its degree is the rank of the
locally free $\mathcal{O}_B$-module $f_* \mathcal{O}_A$, which is the rank function
`Scheme.Hom.finrank` of the underlying morphism.

Over a field this is the usual notion: a surjective homomorphism of abelian varieties with finite
kernel is finite and flat. See J. S. Milne, *Abelian Varieties*, course notes, version 2.00
(2008), Chapter I, §7, <https://www.jmilne.org/math/CourseNotes/AV.pdf>.
