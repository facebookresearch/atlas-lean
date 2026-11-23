# Order reduction for marked ideals

This node is still to be broken down: the statement is precise, but its proof, which occupies most of
Kollár's lecture, is not.

Let $X$ be a smooth scheme of finite type over a field of characteristic zero. A *marked ideal sheaf* on
$X$ is a pair $(I, m)$ of an ideal sheaf $I \subset \mathcal{O}_X$ and an integer $m \ge 0$; its
cosupport $\operatorname{cosupp}(I, m)$ is the set of points where $I$ has order at least $m$, and
$\operatorname{max\text{-}ord} I$ is the maximal order of $I$ at points of $X$. A smooth blow-up sequence
of order $\ge m$ starting with $(X, I, m, E)$, for $E$ a divisor with snc support whose components are
indexed by an ordered set, blows up smooth centres contained in the cosupports of the successive
birational transforms $(I_j, m)$, $I_{j+1} = \mathcal{O}(m F_j) \cdot \pi_j^* I_j$, with $F_j$ the
exceptional divisor, and adds the exceptional divisors to $E$.

**Theorem** (Kollár, Theorem 69). For every $m$ there is a smooth blow-up sequence functor
$BMO_m$ of order $\ge m$, defined on triples $(X, I, m, E)$ as above, such that if
$BMO_m(X, I, m, E)$ ends with $(X_r, I_r, m, E_r)$, then $\operatorname{max\text{-}ord} I_r < m$, and
$BMO_m$ commutes with smooth morphisms and with change of fields. Moreover (Claim 71.2), for a closed
embedding $\tau \colon Y \hookrightarrow X$ of smooth schemes and ideal sheaves $J \subset \mathcal{O}_Y$,
nonzero on every irreducible component of $Y$, and $I \subset \mathcal{O}_X$ with
$\tau_*(\mathcal{O}_Y / J) = \mathcal{O}_X / I$, one has $BMO_1(X, I, 1, \emptyset) =
\tau_* BMO_1(Y, J, 1, \emptyset)$; Kollár notes that this compatibility can fail when $E \ne \emptyset$.

A good expansion follows Kollár's lecture and has pages for: marked ideals, their birational transforms
and the inductive setup (§§5–6); birational transforms of derivatives (§7); maximal contact, going down
and going up (§§8–9); uniqueness of maximal contact and tuning of ideals (§§10–11); order reduction for
ideals (§12); and order reduction for marked ideals (§13), that is, the two inductive steps 70.1 and 70.2,
from order reduction in dimension $n - 1$ to order reduction for ideals of maximal order in dimension $n$
(Theorem 68) and from there to order reduction for marked ideals in dimension $n$, with the proof of
Claim 71.2.

## Depends on

- [Simple normal crossing divisor](simple-normal-crossing-divisor.md), for blow-up sequences, blow-up
  sequence functors and divisors with snc support

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: §4, 49 (order reduction theorems, marked ideal sheaves and
  their birational transforms), pp. 30–31; §§5–6, pp. 36–43; Theorems 68 and 69, 70 (the main inductive
  steps), 71 with Claims 71.1–71.2 and the remark that follows, pp. 41–42; §§7–13, pp. 43–67.
