# Resolution of singularities of quasi-projective varieties

Let $X$ be a quasi-projective variety over a field of characteristic zero. There is a birational
projective morphism $\Pi \colon R(X) \to X$ such that

1. $R(X)$ is smooth;
2. $\Pi$ is an isomorphism over the smooth locus $X^{\mathrm{ns}} = X \setminus \operatorname{Sing} X$;
3. $\Pi^{-1}(\operatorname{Sing} X)$ is a divisor with
   [simple normal crossings](simple-normal-crossing-divisor.md).

This is Hironaka's theorem, in the form that Kollár calls a strong resolution (Theorem 27).

Kollár obtains it from [principalization](principalization-of-ideal-sheaves.md) in a smooth ambient
variety. Embed $X$ into a smooth variety $P$ with $\dim P \ge \dim X + 2$, for instance
$P = \mathbb{P}^N$ with $N$ large, let $\bar X$ be the closure of $X$ and $I \subset \mathcal{O}_P$ its
ideal sheaf, and apply principalization to $(P, I, \emptyset)$. As $\bar X$ has codimension at least
$2$, $I$ is not locally principal at the generic point of $X$, so some blow-up centre contains this
point; let $Z_j \subset P_j$ be the first such centre and, if it is disconnected, replace it by its
connected component dominating $\bar X$; the composite of the earlier blow-ups restricts to a birational
morphism $g \colon Z_j \to \bar X$ from this smooth variety (Corollary 22 and its proof). The functoriality of principalization for smooth morphisms, together with the fact that any
two smooth points of $X$ have isomorphic étale neighbourhoods in their embeddings into $P$, shows that
$g$ is an isomorphism over the smooth locus of $\bar X$; and
$g^{-1}(\operatorname{Sing} \bar X) = Z_j \cap \mathrm{Ex}_{\mathrm{tot}}(\pi_0 \circ \dots \circ \pi_{j-1})$
is an snc divisor on $Z_j$, because $Z_j$ has simple normal crossings with the total exceptional set
of the earlier blow-ups. One takes $R(X) = g^{-1}(X)$.

The resolution obtained this way need not be a composite of blow-ups of smooth centres: it is the
composite of the blow-ups of $X$ whose centres are the intersections of the smooth centres $Z_i$ with
the birational transforms of $X$, and these intersections may be singular (Warning 23 and
Example 106). Kollár does not claim that it is independent of the embedding $X \hookrightarrow P$;
the [functorial resolution of schemes of finite
type](functorial-resolution-of-schemes-of-finite-type.md) settles this. The argument applies to every
scheme that embeds into a smooth variety, but not every scheme does (Remark 28 and Aside 46).

## Depends on

- [Simple normal crossing divisor](simple-normal-crossing-divisor.md)

## Proof depends on

- [Principalization of ideal sheaves in characteristic zero](principalization-of-ideal-sheaves.md), for
  the case $E = \emptyset$ of Theorems 26 and 35, applied to the ideal sheaf of the closure of $X$ in a
  smooth ambient variety

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: Theorem 27 (Resolution of singularities, II) and its proof,
  pp. 19–20; Corollary 22 with its proof and Warning 23, pp. 17–18; Remark 28, p. 20; Aside 46,
  pp. 28–29; Example 106, p. 63; the notion of strong resolution, 3, p. 4. Sections 1–13 of the
  lecture are Sections 3.1–3.13 of the chapter "Strong resolution in characteristic zero" of
  J. Kollár, *Lectures on Resolution of Singularities*, Annals of Mathematics Studies 166, Princeton
  University Press, 2007.
- H. Hironaka, "Resolution of singularities of an algebraic variety over a field of characteristic
  zero. I, II", Ann. of Math. (2) 79 (1964), 109–203 and 205–326.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses a related
  statement, for reduced separated schemes of finite type with $\Pi$ a sequence of blow-ups, as
  `GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero`.
