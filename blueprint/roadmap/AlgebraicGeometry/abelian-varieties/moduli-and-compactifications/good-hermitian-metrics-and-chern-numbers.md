# Good hermitian metrics and Chern numbers

This node is still to be broken down. It covers Mumford's theory of good singular hermitian metrics
on vector bundles over the complement of a normal crossing divisor, a flag push-forward identity for
Chern numbers, and Hirzebruch–Mumford proportionality, which is applied to toroidal
compactifications of moduli spaces such as those of polarized
[abelian varieties](moduli-of-principally-polarized-abelian-varieties.md). Let $\bar X$ be a smooth
projective complex variety of dimension $n$, $D \subset \bar X$ a divisor with normal crossings, $X
= \bar X \setminus D$, and $\bar E$ a vector bundle of rank $r$ on $\bar X$ with a hermitian metric
$h$ on $E = \bar E|_X$. The targets are:

1. (Good metrics.) The metric $h$ is *good* if every point of $D$ has a coordinate neighbourhood $V$
   with $D \cap V = \{z_1 \cdots z_k = 0\}$ and a holomorphic frame $e_1, \dots, e_r$ of $\bar E$ on
   $V$ such that, for $h_{ij} = h(e_i, e_j)$: (i) $|h_{ij}|$ and $(\det h)^{-1}$ are bounded by a
   constant times $\bigl(\prod_{i \le k} \log(1/|z_i|)\bigr)^N$ for some $N$, a **power** of the
   logarithms, not only a logarithmic bound (the metric $(\log(1/|z|))^2$ on the trivial line bundle
   of the punctured disc is good); and (ii) the connection forms $(\partial h \cdot h^{-1})_{ij}$
   are good forms, that is, they and their differentials have Poincaré growth along $D$. For a good
   metric the Chern forms of $(E, h)$ are good forms, locally integrable on $\bar X$, and the
   currents they define represent the Chern classes of $\bar E$ (Mumford, Theorem 1.4). In
   particular, for every polynomial $R$ in the Chern classes of weighted degree $n$, the $k$-th
   Chern class having weight $k$, the Chern number $\int_{\bar X} R(c(\bar E))$ is the integral over
   $X$ of the form $R(c(E, h))$.
2. (Flag push-forward on a flag refinement, an unsourced identity in the form stated.) Let $Y$ be a
   smooth projective variety over a field of characteristic zero with a morphism $f \colon Y \to
   \bar X$, and $\bar E_\tau$, for $\tau$ in a finite set, vector bundles on $\bar X$ of ranks
   $m_\tau$. A *flag refinement* consists of full flags of the bundles $f^* \bar E_\tau$ whose
   successive quotients are line bundles $\mathcal{O}(\Delta_{\tau, i})$, $0 \le i < m_\tau$, for
   divisors $\Delta_{\tau, i}$ on $Y$ (the divisors of the diagonal entries of the change from one
   generic frame adapted to the flags to local adapted frames), such that, for every field $K$,
   every $K$-point $x$ of $\bar X$ and every choice of full flags of the fibres $\bar E_\tau(x)
   \otimes K$, there is exactly one $K$-point of $Y$ over $x$ at which the flags of the $f^* \bar
   E_\tau$ are the chosen ones. On points, $Y$ is then the fibre product over $\bar X$ of the
   complete flag bundles of the $\bar E_\tau$, and $\dim Y = \dim \bar X + \sum_\tau m_\tau (m_\tau -
   1)/2$. The lifting condition cannot be dropped: for $\bar X = Y = \mathbb{P}^1$, $f =
   \mathrm{id}$ and $\bar E = \mathcal{O}(1) \oplus \mathcal{O}$ with its split flag, whose
   quotients have degrees $1$ and $0$, the polynomials $Q = x_0 + x_1$ and $R = 0$ below satisfy the
   hypothesis of the target but $\langle Q \rangle_Y = 1$ while $\langle \mathrm{cr}(R) \cdot
   \mathrm{fp} \rangle_Y = 0$.

   In the polynomial ring in roots $x_{\tau, i}$, let $\mathrm{cr}(R)$ substitute, for the $k$-th
   Chern class of $\bar E_\tau$, the $k$-th elementary symmetric polynomial of $x_{\tau, 0}, \dots,
   x_{\tau, m_\tau - 1}$; let $\mathrm{fp} = \prod_{\tau, i} (-x_{\tau, i})^{m_\tau - 1 - i}$ and
   $\delta = \prod_\tau \prod_{i < j} (x_{\tau, j} - x_{\tau, i})$; and let $\operatorname{alt}(Q) =
   \sum_w \operatorname{sign}(w)\, w \cdot Q$, over $w \in \prod_\tau S_{m_\tau}$ permuting the
   roots of each $\tau$. For a polynomial $Q$ in the roots, write $\langle Q \rangle_Y$ for the sum
   of the intersection numbers on $Y$ of the divisors $\Delta_{\tau, i}$ given by the monomials of
   $Q$ of degree $\dim Y$. The target is: for a flag refinement, **if** $\operatorname{alt}(Q) =
   \mathrm{cr}(R) \cdot \delta$, **then** $\langle Q \rangle_Y = \langle \mathrm{cr}(R) \cdot
   \mathrm{fp} \rangle_Y$. On the complete flag bundle itself, with its tautological flags, the
   Gysin formula (Darondeau–Pragacz, §1.2 and Theorem 1.1) computes the push-forward of a polynomial
   in the Chern roots (their variables are the negatives of the first Chern classes of the
   tautological quotients, in reverse order) as an antisymmetrization divided by the discriminant.
   That this classical formula gives the identity above, with these orderings, signs and the
   normalization $\mathrm{fp}$ of the class of a point of the fibre, and that every flag refinement
   has the intersection numbers of the complete flag bundle, are part of this target; no source
   states them in this form.
3. (Proportionality.) Let $\Gamma$ be a neat arithmetic group acting on a bounded symmetric domain
   $\mathcal{D}$ with compact dual $\check{\mathcal{D}}$, and $\bar X$ a smooth toroidal
   compactification of $\Gamma \backslash \mathcal{D}$. There is a constant $c$ such that, for every
   polynomial $p$ in the Chern classes of weighted degree $n$ and every equivariant vector bundle
   $E_0$ on $\check{\mathcal{D}}$, with $\bar E$ the canonical extension of the automorphic bundle
   it defines, $p(c(\bar E)) = c \cdot p(c(E_0))$ as top-degree Chern numbers (Mumford, §3; Hörmann,
   Theorem 4.2.1, algebraically, for abstract toroidal compactifications with automorphic data with
   logarithmic connection satisfying his axioms (F, T, M, B) and with $P_M$ reductive). Neatness, or
   at least freeness of the action, is needed for the automorphic bundles to be vector bundles on
   the quotient: on a coarse quotient a stabilizer acting nontrivially on a homogeneous bundle can
   prevent descent (already $-1$ on the Hodge line of elliptic curves), and without it the statement
   concerns the quotient stack with its own integration convention. The form used by Alpöge's
   library, for unitary Shimura varieties, expresses intersection numbers of the weight line bundles
   on a flag refinement, as in 2, of a toroidal compactification as the covolume of the component
   times a flag degree computed on the compact dual; its normalization of $c$ as a covolume is part
   of the target.

A good expansion has pages for: good forms and good metrics, and Mumford's Theorem 1.4 (Mumford, §1;
Burgos Gil–Kramer–Kühn, §1.5, Definition 3.25 and Proposition 3.27); the Gysin formula for flag
bundles and its conversion into the identity 2; the canonical extensions of automorphic vector
bundles to toroidal compactifications with their good invariant metrics (Mumford, §§2–3); and
proportionality, with the constant, in the form 3. The general statements 1 and 2 do not depend on
the moduli application, which is the concern of 3 and of the pages it uses.

## Depends on

- [Toroidal compactifications of unitary Shimura varieties](toroidal-compactifications-of-unitary-shimura-varieties.md),
  for the compactifications in the library's form of 3

## Proof depends on

- [Toroidal compactifications of unitary Shimura varieties](toroidal-compactifications-of-unitary-shimura-varieties.md),
  for the toroidal compactifications in the unitary application of 3, not for the proportionality
  factor or the push-forward along flag bundles

## Sources

- D. Mumford, "Hirzebruch's proportionality theorem in the non-compact case", Invent. Math. 42
  (1977), 239–272: §1 (good forms and good metrics, Theorem 1.4) and §3 (proportionality).
- J. I. Burgos Gil, J. Kramer and U. Kühn, "Arithmetic characteristic classes of automorphic vector
  bundles", arXiv:math/0502085: §1.5 (good forms, p. 38), Definition 3.25 and Proposition 3.27 (good
  metrics, after Mumford, pp. 63–64).
- L. Darondeau and P. Pragacz, "Universal Gysin formulas for flag bundles", arXiv:1510.07852
  (version 4): §1.2 and Theorem 1.1 (push-forward from flag bundles).
- F. Hörmann, "Generalized automorphic sheaves and the proportionality principle of
  Hirzebruch–Mumford", preprint (5 June 2019): introduction, p. 1 (neat groups), and Theorem 4.2.1.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1 and 2 as `GlobalTheory.Published.GoodChernWeil`, the conjunction of `GoodChernNumbers`
  (the integral of $R$ for a good metric equals $\langle \mathrm{cr}(R) \cdot \mathrm{fp} \rangle_Y$
  on a flag refinement $Y \to \bar X$ as in 2) and `FlagPushForward` (the implication of 2, with
  `antisymm`, `chernRoots`, `rootDiscr`, `fibrePoint` and `interPoly` as above), both for flag
  refinements in the sense of its predicates `Refines` (with the lifting condition `lifts`) and
  `IsGraded`, and 3 for unitary Shimura varieties as
  `GlobalTheory.Published.MumfordProportionality`; no published source stating them in this form has
  been identified.
