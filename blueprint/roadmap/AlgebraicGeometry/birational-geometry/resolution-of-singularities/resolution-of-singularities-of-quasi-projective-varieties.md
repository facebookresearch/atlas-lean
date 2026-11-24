# Resolution of singularities of quasi-projective varieties

Let $X$ be an integral quasi-projective variety over a field of characteristic zero. There is a
birational projective morphism $\Pi \colon R(X) \to X$ such that

1. $R(X)$ is smooth;
2. $\Pi$ is an isomorphism over the smooth locus $X^{\mathrm{ns}} = X \setminus \operatorname{Sing}
   X$;
3. $\Pi^{-1}(\operatorname{Sing} X)$, with its reduced structure, is a divisor with
   [simple normal crossings](../simple-normal-crossing-divisor.md).

This is Hironaka's theorem, in the form that Kollár calls a strong resolution (Theorem 27). Item 3
is a statement about sets: Kollár separates the stronger scheme-theoretic condition (§3, p. 4). For
the cusp $\operatorname{Spec} k[t^2, t^3]$, the ideal of the reduced singular point pulls back on
the normalization to $(t^2, t^3) = (t^2)$, which is not the ideal of a reduced divisor.

Kollár obtains it from [principalization](principalization-of-ideal-sheaves.md) in a smooth ambient
variety. Embed $X$ into a smooth variety $P$ with $\dim P \ge \dim X + 2$, for instance $P =
\mathbb{P}^N$ with $N$ large, let $\bar X$ be the closure of $X$ and $I \subset \mathcal{O}_P$ its
ideal sheaf, and apply principalization to $(P, I, \emptyset)$. As $\bar X$ has codimension at least
$2$, $I$ is not locally principal at the generic point of $X$, so some blow-up centre contains this
point; let $Z_j \subset P_j$ be the first such centre and, if it is disconnected, replace it by its
connected component dominating $\bar X$; the composite of the earlier blow-ups restricts to a
birational morphism $g \colon Z_j \to \bar X$ from this smooth variety (Corollary 22 and its proof).
The functoriality of principalization for smooth morphisms at every step (Theorem 35), together with
étale coordinates for the embedded pair at smooth closed points of $\bar X$ (after the change of
fields to an algebraic closure, with which principalization commutes, any two smooth closed points
of $\bar X$ have isomorphic pointed étale neighbourhoods in their embeddings into $P$; points with
different residue fields, such as the generic point and a closed point of a curve, do not), shows
that $g$ is an isomorphism over the smooth locus of $\bar X$ (with Theorem 26 alone, functorial only
for the end result, Kollár argues instead with the final strict transform of the dominating
exceptional divisor, generic smoothness and the factorization through $Z_j$, p. 20); and
$g^{-1}(\operatorname{Sing} \bar X) = Z_j \cap \mathrm{Ex}_{\mathrm{tot}}(\pi_0 \circ \dots \circ
\pi_{j-1})$ is an snc divisor on $Z_j$, because $Z_j$ has simple normal crossings with the total
exceptional set of the earlier blow-ups. One takes $R(X) = g^{-1}(X)$.

The resolution obtained this way need not be a composite of blow-ups of smooth centres: it is the
composite of the blow-ups of $X$ whose centres are the intersections of the smooth centres $Z_i$
with the birational transforms of $X$, and these intersections may be singular (Warning 23 and
Example 106). Kollár does not claim that it is independent of the embedding $X \hookrightarrow P$;
the
[functorial resolution of schemes of finite type](functorial-resolution-of-schemes-of-finite-type.md)
settles this. For a scheme that embeds into a smooth variety the embedding method extends in the
scheme form of that functorial resolution (Kollár, Theorem 36), not with the birational conclusion
of Theorem 27: $\operatorname{Spec} k[\varepsilon]/(\varepsilon^2)$ embeds into an affine space but
has no dense open subscheme that is smooth. Not every scheme embeds into a smooth variety (Remark 28
and Aside 46).

## Depends on

- [Simple normal crossing divisor](../simple-normal-crossing-divisor.md)
- [Geometrically reduced variety over a field](../../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the underlying variety over a field, which the statement takes integral and quasi-projective

## Proof depends on

- [Principalization of ideal sheaves in characteristic zero](principalization-of-ideal-sheaves.md), for
  the case $E = \emptyset$ of Theorems 26 and 35, applied to the ideal sheaf of the closure of $X$ in a
  smooth ambient variety
- [Blow-ups along smooth centres and total transforms](blow-ups-along-smooth-centres.md), for the
  total exceptional set of the earlier blow-ups

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: Theorem 27 (Resolution of singularities, II) and its
  proof, pp. 19–20; Corollary 22 with its proof and Warning 23, pp. 17–18; Remark 28, p. 20; Aside
  46, pp. 28–29; Example 106, pp. 63–64; the notion of strong resolution, 3, p. 4. Sections 1–13 of
  the lecture are Sections 3.1–3.13 of the chapter "Strong resolution in characteristic zero" of J.
  Kollár, *Lectures on Resolution of Singularities*, Annals of Mathematics Studies 166, Princeton
  University Press, 2007.
- H. Hironaka, "Resolution of singularities of an algebraic variety over a field of characteristic
  zero. I, II", Ann. of Math. (2) 79 (1964), 109–203 and 205–326.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses a related statement, for reduced separated schemes of finite type with $\Pi$ a sequence of
  blow-ups, as `GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero`.
