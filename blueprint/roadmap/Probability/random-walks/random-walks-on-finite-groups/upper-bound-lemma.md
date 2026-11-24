# Upper bound lemma (Diaconis–Shahshahani)

Let $G$ be a finite group and let $V_i$ ($i \in \iota$) be a complete set of irreducible complex
representations of $G$: pairwise non-isomorphic irreducible finite-dimensional complex
representations, every irreducible one being isomorphic to one of them. Write $d_i$ for the
dimension of $V_i$ and $\hat Q(V_i) = \sum_s Q(s)\, V_i(s)$ for the Fourier transform of
$Q : G \to \mathbb{C}$. Let $P : G \to \mathbb{R}$ have total mass $1$, let $P^\vee(s) = P(s^{-1})$
and let $U$ be the uniform distribution. Then

$$4\,\|P - U\|_{TV}^2 \le \sum_{i \,:\, V_i \text{ non-trivial}} d_i \operatorname{Re}\operatorname{Tr}\bigl(\hat P(V_i)\, \hat{P^\vee}(V_i)\bigr),$$

where $V_i$ is non-trivial when some $V_i(g)$ is not the identity, and
$\|P - U\|_{TV} = \tfrac12 \sum_s |P(s) - U(s)|$.

The source takes each $V_i(s)$ unitary; then, $P$ being real, $\hat{P^\vee}(V_i) = \hat P(V_i)^*$,
and the right side is $\sum_i d_i \operatorname{Re}\operatorname{Tr}(\hat P(V_i)\, \hat P(V_i)^*)$,
which needs no choice of inner product in the form above. The Saint-Flour notes print the lemma
with $=$; their proof (Cauchy–Schwarz, then Plancherel) gives $\le$, which is what is stated.

The proof is Diaconis's: with $f = P - U$, Cauchy–Schwarz gives
$(\sum_s |f(s)|)^2 \le |G| \sum_s f(s)^2$; the [Plancherel formula](../../../RepresentationTheory/finite-group-representations/fourier-transform-on-finite-groups/plancherel.md)
turns the right side into $\sum_i d_i \operatorname{Tr}(\hat f(V_i) \hat f(V_i)^*)$; the trivial
term vanishes because $f$ has total mass $0$, and $\hat f(V_i) = \hat P(V_i)$ for non-trivial
$V_i$ because [the uniform distribution has zero transform there](../../../RepresentationTheory/finite-group-representations/fourier-transform-on-finite-groups/fourier-uniform-eq-zero.md).

For a finite abelian group every $d_i = 1$ and the $V_i$ are the characters; that case is stated
with the discrete Fourier transform in
[Upper bound lemma on a finite abelian group](four-mul-tv-dist-uniform-sq-le.md).

## Background

- [Total variation distance of functions on a finite set](../../markov-chains/mixing-times-of-markov-chains/tv-dist.md): the
  distance being bounded, with the same factor $\tfrac12$.

## Sources

- P. Diaconis, *Applications of non-commutative Fourier analysis to probability problems*,
  École d'Été de Probabilités de Saint-Flour XV–XVII, Lecture Notes in Math. 1362 (1988),
  Lemma 4.2 ("first used by Diaconis and Shahshahani (1981)").
