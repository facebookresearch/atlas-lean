# Principalization of ideal sheaves in characteristic zero

There is a [blow-up sequence functor](simple-normal-crossing-divisor.md) $BP$, defined on all triples
$(X, I, E)$ in which $X$ is a smooth scheme of finite type over a field of characteristic zero,
$I \subset \mathcal{O}_X$ is an ideal sheaf that is not zero on any irreducible component of $X$, and
$E$ is a [simple normal crossing divisor](simple-normal-crossing-divisor.md) on $X$, such that the
blow-up sequence $BP(X, I, E) = (\Pi \colon X_r \to \dots \to X_0 = X)$ satisfies:

1. all centres of the blow-ups are smooth and have simple normal crossings with $E$;
2. the inverse image ideal sheaf $\Pi^* I = \Pi^{-1} I \cdot \mathcal{O}_{X_r}$ is locally monomial:
   $\Pi^* I = \mathcal{O}_{X_r}(-F)$ for an effective divisor $F$ with
   [simple normal crossing support](simple-normal-crossing-divisor.md), whose multiplicities may exceed
   $1$;
3. when $E = \emptyset$, $\Pi$ is an isomorphism over $X \setminus \operatorname{cosupp} I$, where
   $\operatorname{cosupp} I = \operatorname{Supp}(\mathcal{O}_X / I)$;
4. $BP$ commutes with smooth morphisms and with change of fields;
5. $BP$ commutes with closed embeddings when $E = \emptyset$: if $j \colon Y \hookrightarrow X$ is a
   closed embedding of smooth schemes and $I_Y \subset \mathcal{O}_Y$, $I_X \subset \mathcal{O}_X$ are
   nonzero ideal sheaves with $\mathcal{O}_X / I_X = j_*(\mathcal{O}_Y / I_Y)$, then
   $BP(X, I_X, \emptyset)$ is the push-forward of $BP(Y, I_Y, \emptyset)$, the blow-up sequence of $X$
   whose centres are the images of the centres of $BP(Y, I_Y, \emptyset)$.

As $\Pi$ is a composite of smooth blow-ups, $X_r$ is smooth and $\Pi$ is projective. The divisor $F$
need not be reduced: for $I = (x^2)$ on the affine line, every blow-up with centre in $\operatorname{cosupp}
I$ is the blow-up of a Cartier divisor, hence an isomorphism, and $\Pi^* I = (x^2)$ remains non-reduced.
In Kollár's construction $F = \sum_{j} \Pi_{r,j+1}^* F_j$, where $F_j$ is the exceptional divisor of the
$j$-th blow-up in his sense (for a trivial blow-up, the Cartier centre itself) and $\Pi_{r, j+1}$ the
composite of the later blow-ups (proof of Theorem 35 in 72); for $E = \emptyset$ the support of $F$ is
therefore the total exceptional set $\mathrm{Ex}_{\mathrm{tot}}(\Pi)$, an snc divisor. Kollár states
item 3 for every triple; for $E \ne \emptyset$ his construction begins with blow-ups that separate the
components of $E$, whose centres need not lie in $\operatorname{cosupp} I$, so the statement is restricted
here to $E = \emptyset$, the case used for resolution.

This is Kollár's strongest form of principalization (Theorem 35). For a smooth variety $X$ over a field
of characteristic zero and a nonzero ideal sheaf $I$ he first states three weaker forms: there is a
smooth variety $X'$ with a birational projective morphism $f \colon X' \to X$ such that $f^* I$ is
locally principal (Theorem 17); $f$ can be chosen to be an isomorphism over
$X \setminus \operatorname{cosupp} I$ and a composite of smooth blow-ups (Theorem 21); and, for an snc
divisor $E$ on $X$, there is a sequence of smooth blow-ups $\Pi$ whose centres have simple normal
crossings with $E$, such that $\Pi^* I$ is the ideal sheaf of an snc divisor and $\Pi$ is functorial for
smooth morphisms (Theorem 26). Theorem 26 asserts this functoriality for the end result $\Pi$ only, not
for the intermediate blow-ups; blow-up sequence functors record it at every step, which is what the
deduction of resolution theorems from principalization needs (Kollár, proof of Theorem 27, and 28–34).

Principalization in characteristic zero goes back to Hironaka (1964), whose starting point Kollár
describes as "a profound shift in emphasis from resolving singularities of varieties to resolving
'singularities of ideal sheaves'". Kollár's proof relies mostly on the works of Villamayor and
Włodarczyk and occupies Sections 4–13 of the lecture: Theorem 35 is deduced in 72 from
[order reduction for marked ideals](order-reduction-for-marked-ideals.md) (Theorem 69) and its
compatibility with closed embeddings (Claim 71.2), after the preliminary blow-ups that make the
components of $E$ disjoint.

## Depends on

- [Simple normal crossing divisor](simple-normal-crossing-divisor.md), for snc divisors, divisors with snc
  support, centres having simple normal crossings with $E$, total transforms and blow-up sequence
  functors

## Proof depends on

- [Order reduction for marked ideals](order-reduction-for-marked-ideals.md), for Kollár's Theorem 69 and
  Claim 71.2

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: Theorem 35 (Principalization, IV) with 34.1–34.3,
  pp. 23–25; Theorems 17, 21 and 26 (Principalization, I–III), pp. 16–19; 16 (monomial ideals),
  p. 16; the proof of Theorem 27, pp. 19–20; Theorems 68–69, 71 (with Claim 71.2 and the remark after
  it on the case $E \ne \emptyset$) and 72 (the deduction of Theorem 35), pp. 41–43; the introduction, pp. 1–2. Sections 1–13 of the lecture are Sections 3.1–3.13 of the
  chapter "Strong resolution in characteristic zero" of J. Kollár, *Lectures on Resolution of
  Singularities*, Annals of Mathematics Studies 166, Princeton University Press, 2007.
- H. Hironaka, "Resolution of singularities of an algebraic variety over a field of characteristic
  zero. I, II", Ann. of Math. (2) 79 (1964), 109–203 and 205–326.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result in a
  specialised form, for $X$ smooth of pure dimension, quasi-compact and separated over the field, and
  without the functoriality, as `GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero`.
