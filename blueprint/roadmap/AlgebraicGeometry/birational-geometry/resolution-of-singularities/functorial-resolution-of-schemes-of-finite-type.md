# Functorial resolution of schemes of finite type in characteristic zero

This node is still to be broken down: the statement is precise, but the construction is spelled out
only for varieties.

There is a [blow-up sequence functor](../simple-normal-crossing-divisor.md) $BR$ that assigns to
every scheme $X$ of finite type over a field of characteristic zero a blow-up sequence

$$BR(X) = \bigl(\Pi \colon X_r \to X_{r-1} \to \dots \to X_1 \to X_0 = X\bigr)$$

with specified centres $Z_i \subset X_i$, such that

1. $X_r$ is smooth;
2. $\Pi$ is an isomorphism over the smooth locus $X^{\mathrm{ns}}$ of $X$;
3. $\Pi^{-1}(\operatorname{Sing} X)$, with its reduced structure, is a divisor with
   [simple normal crossings](../simple-normal-crossing-divisor.md);
4. $BR$ commutes with smooth morphisms and with change of fields: for every smooth surjective
   morphism $h \colon Y \to X$, $BR(Y)$ is the pull-back $h^* BR(X)$; for every smooth morphism $h$,
   $BR(Y)$ is obtained from $h^* BR(X)$ by deleting the blow-ups with empty centre and renumbering;
   and for every extension $\sigma \colon K \hookrightarrow L$ of the base field $K$, $BR(X
   \times_{\operatorname{Spec} K} \operatorname{Spec} L)$ is the base change of $BR(X)$.

Kollár states this (Theorem 36) for all schemes of finite type over the field: $X$ is not assumed to
be reduced or irreducible, and the proof first constructs $BR$ on possibly reducible affine schemes.
The conclusions do not include that $\Pi$ is birational, unlike those of the
[resolution of quasi-projective varieties](resolution-of-singularities-of-quasi-projective-varieties.md),
and the centres $Z_i$ need not be smooth: the restriction of a smooth blow-up sequence to a closed
subscheme need not be a smooth blow-up sequence (30.2 and Warning 23).

Kollár's proof (Theorem 36 and Proposition 37). For affine $X$, choose a closed embedding of $X$
into an affine space $A = \mathbb{A}^N$ of large dimension, so that $X$ has codimension at least $2$
at every point, with ideal sheaf $I_X$, which is then nonzero on $A$. (An inequality of total
dimensions does not suffice for a disconnected smooth ambient scheme: in $A = \mathbb{A}^1 \sqcup
\mathbb{A}^3$, $X = \mathbb{A}^1$ embedded as the first component has an ideal that vanishes on a
component, outside the domain of $BP$.) For an affine **variety** $X$, as in the proof of Corollary
22, the blow-up sequence of [principalization](principalization-of-ideal-sheaves.md) $BP(A, I_X,
\emptyset)$ gives a blow-up sequence $BR(X)$: one restricts to the strict transforms of $X$ the
blow-ups that come before the first centre containing the generic point of the strict transform of
$X$, and stops there, since restricting that blow-up as well would give $B_X X = \emptyset$ for $X$
smooth of codimension $2$ (30.2). This stopping rule is not a construction for arbitrary schemes,
and Kollár's "as in (22)" (p. 25) does not supply one. For the fat point $X = V(y, x^2) \subset
\mathbb{A}^2_k$, whose only point is generic, the ideal is not principal at that point, so some
centre meets it, and the blow-ups before the first such centre are isomorphisms near $X$: stopping
there returns $X$ itself, which is not smooth. Several irreducible components may also call for
different stopping steps. A construction for nonreduced and reducible schemes, with its proof, is
what remains to be broken down; for such an input the terminal scheme may be empty (blowing up the
fat point along its nilpotent ideal gives the empty scheme), which items 1–3 allow. The sequence
obtained for a variety does not depend on the embedding, because $BP$ is compatible with closed
embeddings (in the weak form 34.4) and any two closed embeddings of $X$ into affine spaces become
equivalent under an automorphism of a larger affine space (Lemma 39). The compatibility with change
of fields and with smooth morphisms reduces to the same properties of $BP$, through Lemma 41 for
smooth morphisms. Finally, a blow-up sequence functor defined on affine schemes over a field $k$ and
commuting with smooth surjections has a unique extension to all schemes of finite type over $k$
commuting with smooth surjections (Proposition 37): for a finite affine open cover $X = \bigcup_i
U_i$, the blow-up sequence of the affine scheme $\coprod_i U_i$ descends to $X$, which is why $BR$
has to be defined on disconnected affine schemes (Warning 38).

## Depends on

- [Simple normal crossing divisor](../simple-normal-crossing-divisor.md), for snc divisors, blow-up
  sequences and blow-up sequence functors

## Proof depends on

- [Principalization of ideal sheaves in characteristic zero](principalization-of-ideal-sheaves.md), for
  Theorem 35 with $E = \emptyset$, including its compatibility with smooth morphisms, change of fields
  and closed embeddings
- [Embeddings and descent for blow-up sequence functors](embedding-and-descent-for-blow-up-sequence-functors.md),
  for Proposition 37 and Lemmas 39 and 41

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: Theorem 36 (Resolution of singularities, III) and its
  proof, pp. 25–26; Proposition 37 and Warning 38, p. 26; Lemmas 39 and 41, p. 27; 30.2 (restriction
  of blow-up sequences), p. 22; 34.1–34.4, pp. 23–24; Corollary 22 and Warning 23, pp. 17–18.
  Sections 1–13 of the lecture are Sections 3.1–3.13 of the chapter "Strong resolution in
  characteristic zero" of J. Kollár, *Lectures on Resolution of Singularities*, Annals of
  Mathematics Studies 166, Princeton University Press, 2007.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses this result in a specialised form, for reduced separated schemes of finite type and without
  the functoriality, as `GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero`.
