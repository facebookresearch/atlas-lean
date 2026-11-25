# Principalization relative to a simple normal crossing divisor

Let $M$ be a smooth separated scheme of finite type over a field of characteristic zero, possibly
disconnected, $E = H_1 + \dots + H_s$ a
[simple normal crossing divisor](../simple-normal-crossing-divisor.md) on $M$ with smooth members
$H_i$, taken in this order (any order will do for the existence statement below; the order is not
canonical), and $I \subset \mathcal{O}_M$ a coherent ideal sheaf that is nonzero on every
irreducible component of $M$ (Bierstone and Milman also allow an ideal that vanishes on a component,
which is then blown up whole; that case is excluded here). A blow-up $\sigma \colon M' \to M$ with
smooth centre $C$ is *admissible* for $(I, E)$ if $C \subset V(I)$ and $C$ has simple normal
crossings with $E$; the *transform* of $(I, E)$ is then $(I', E')$, with $I' =
\mathcal{I}_{\sigma^{-1}(C)}^{-1} \cdot \sigma^* I$, obtained by removing one factor of the ideal of
the exceptional divisor $\sigma^{-1}(C)$, and $E'$ the sum of the strict transforms of the $H_i$, in
order, followed by $\sigma^{-1}(C)$.

**Theorem** (Bierstone–Milman). There is a finite sequence of blow-ups with smooth centres

$$M = M_0 \xleftarrow{\ \sigma_1\ } M_1 \leftarrow \dots \xleftarrow{\ \sigma_t\ } M_t,$$

each $\sigma_{j+1}$ admissible for the transform $(I_j, E_j)$ of $(I_{j-1}, E_{j-1})$, with $(I_0,
E_0) = (I, E)$, such that $I_t = \mathcal{O}_{M_t}$. Consequently, for $\sigma = \sigma_1 \circ
\dots \circ \sigma_t$:

1. $M_t$ is smooth, $\sigma$ is projective, and every centre has simple normal crossings with the
   current boundary $E_j$, so that $E_t$ is a simple normal crossing divisor;
2. $\sigma^* I = \mathcal{O}_{M_t}(-F)$ for the effective divisor $F = \sum_{j=1}^t \tau_j^*\,
   \sigma_j^{-1}(C_{j-1})$, with $\tau_j \colon M_t \to M_j$ the composite of the later blow-ups;
   its support is a union of members of $E_t$, so $F$ has simple normal crossing support;
3. $\sigma$ is an isomorphism over $M \setminus V(I)$, for **every** simple normal crossing divisor
   $E$.

This is Bierstone and Milman's resolution of a marked ideal (Theorem 1.3) for the marked ideal $(M,
M, E, I, 1)$, of mark $1$ (Definitions 2.1–2.2): the cosupport of a marked ideal of mark $1$ is
$V(I)$, and the end of the sequence, an empty cosupport, means $I_t = \mathcal{O}_{M_t}$. Since each
step removes exactly one factor of the exceptional ideal, $\sigma_{j+1}^* I_j =
\mathcal{I}_{\sigma_{j+1}^{-1}(C_j)} \cdot I_{j+1}$, which gives 2 by induction. For 3, $I_{j+1}$
agrees with $\sigma_{j+1}^* I_j$ off the exceptional divisor, which lies over $C_j \subset V(I_j)$,
so $V(I_{j+1})$ lies over $V(I_j)$ and every centre lies over $V(I)$. Bierstone and Milman work with
varieties and with reduced separated schemes of finite type, and state that their results extend to
analytic spaces, the sequences of blow-ups being finite over relatively compact open subsets (§1, p.
2); that analytic extension rests on their own construction, not on the algebraic order reduction
below, and is not part of this page.

The boundary must be carried along: principalization in Kollár's form begins, for $E \ne \emptyset$,
with blow-ups that separate the components of $E$, whose centres need not lie in $V(I)$ (for $I =
\mathcal{O}_X$ and $E$ the coordinate axes of $\mathbb{A}^2$ it blows up the origin), so its
sequence need not be an isomorphism off $V(I)$. Here no such blow-up occurs: the centres lie over
$V(I)$ and only need simple normal crossings with the current boundary. The theorem is order
reduction for the marked ideal $(I, 1)$ with boundary $E$, as in
[Kollár's Theorem 69](order-reduction-for-marked-ideals.md) with $m = 1$, applied on each connected
component of $M$; Kollár's blow-up sequences of order $\ge 1$ have the same admissibility conditions
and birational transforms, and his conclusion $\operatorname{max\text{-}ord} I_r < 1$ says $I_r =
\mathcal{O}$.

## Depends on

- [Simple normal crossing divisor](../simple-normal-crossing-divisor.md), for snc divisors, centres having
  simple normal crossings with a divisor and divisors with snc support

## Proof depends on

- [Order reduction for marked ideals](order-reduction-for-marked-ideals.md), for the case $m = 1$ with
  boundary $E$
- [Blow-ups along smooth centres and total transforms](blow-ups-along-smooth-centres.md), for the
  total transforms of the boundary

## Sources

- E. Bierstone and P. D. Milman, "Functoriality in resolution of singularities", arXiv:math/0702375
  (version 1): §1, pp. 2 and 5 (the scope: varieties and reduced separated schemes of finite type,
  with the analytic extension; Theorem 1.3); Definitions 2.1–2.2 (marked ideals, cosupport,
  admissible blowings-up and transforms), pp. 7–8; the proof of Theorem 1.3 in §§5–7, pp. 14–24.
- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: Notation 64, Definitions 65–66 and Theorem 69, pp. 39–41.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the algebraic case, for $M$ smooth of pure dimension, quasi-compact and separated over a
  field of characteristic zero and an ideal $I$ whose cosupport $\operatorname{Supp}(\mathcal{O}_M /
  I)$ contains no irreducible component of $M$, with centres that are smooth over the field and have
  simple normal crossings with the total transform of the boundary, an invertible pull-back with snc
  support and an isomorphism off the support of $\mathcal{O}_M / I$, as
  `GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero`.
