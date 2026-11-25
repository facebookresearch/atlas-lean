# Siegel sets and reduction theory for adelic groups

This node is still to be broken down. It covers the reduction theory of Borel and Harish-Chandra for the
adelic points of a connected reductive group $G$ over a number field $k$, as the theory of automorphic
forms uses it. Fix a minimal parabolic subgroup $P_0$ of $G$ over $k$ with Levi decomposition
$P_0 = M_0 N_0$, the split component $A_0$ of $M_0$, a maximal compact subgroup $K$ of $G(\mathbb{A})$
in good position, the map $H_{P_0} \colon G(\mathbb{A}) \to \mathfrak{a}_0$, the simple roots $\Delta_0$, and
$G(\mathbb{A})^1 = \{x : H_G(x) = 0\}$; here $A_0(\mathbb{R})^0$ is the identity component of the real points of the
maximal $\mathbb{Q}$-split torus in the restriction of scalars of $A_0$ to $\mathbb{Q}$, and the absolute values are
the normalized ones of the [adelic norm](adeles-and-ideles/adelic-norm.md), with the product formula on $k^\times$.

- **Siegel sets.** For $T_1 \in \mathfrak{a}_0$ and a compact subset $\omega$ of
  $N_0(\mathbb{A}) M_0(\mathbb{A})^1$, the Siegel set
  $\mathfrak{S}(T_1, \omega) = \{pak : p \in \omega,\ a \in A_0(\mathbb{R})^0,\ k \in K,\ \beta(H_{P_0}(a) - T_1) > 0 \text{ for } \beta \in \Delta_0\}$.
- **Borel–Harish-Chandra.** One can choose $T_1$ and $\omega$ with
  $G(\mathbb{A}) = G(k)\, \mathfrak{S}(T_1, \omega)$; the quotient $G(k) \backslash G(\mathbb{A})^1$ has finite
  volume, and it is compact if and only if $G$ has no proper parabolic subgroup over $k$ (Borel–Harish-
  Chandra, Mostow–Tamagawa).
- **Finiteness of class numbers** (Borel). For every open compact subgroup $L$ of $G(\mathbb{A}_f)$ the
  double coset space $G(k) \backslash G(\mathbb{A}_f) / L$ is finite, so that $G(k) \backslash G(\mathbb{A}) / L$ is a
  finite union of arithmetic quotients $\Gamma_i \backslash G_\infty$; there are finitely many $G(k)$-conjugacy classes of
  parabolic subgroups over $k$, and, for each arithmetic subgroup $\Gamma$ of $G(k)$, finitely many $\Gamma$-conjugacy
  classes of parabolic subgroups over $k$ (a finer statement: for $\Gamma(2) \subset \mathrm{SL}_2(\mathbb{Z})$ one $G(k)$-class of Borel
  subgroups splits into several $\Gamma$-classes, the cusps).
- **Heights.** For the two-sided height $\lVert x \rVert = \prod_v \max_{i,j}(\lvert r(x)_{ij} \rvert_v, \lvert (r(x)^{-1})_{ij} \rvert_v)$
  defined by a faithful representation $r \colon G \to \mathrm{GL}_m$ over $k$, whose balls are compact (a height
  using only the entries of $r(x)$ need not have this property: on $\mathrm{GL}_1$ over $\mathbb{Q}$ every rational
  point would have height $1$): $\lVert xy \rVert \le m^{[k:\mathbb{Q}]} \lVert x \rVert \lVert y \rVert$ (with the normalized absolute values;
  the constant cannot be dropped for this maximum of entries: for $g = \begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix} \in \mathrm{GL}_2(\mathbb{Q})$,
  $\lVert g \rVert = 1$ and $\lVert g^2 \rVert = 2$), $\lVert x^{-1} \rVert = \lVert x \rVert$, $\#\{\gamma \in G(k) : \lVert \gamma \rVert \le t\} \le C_0 t^{N_0}$, and, on
  a Siegel set $\mathfrak{S}$, $\lVert \delta x \rVert \ge c \lVert x \rVert^{\varepsilon}$ for some $c, \varepsilon > 0$, all $\delta \in G(k)$ and $x \in \mathfrak{S}$ (Arthur, §13, p. 72, proves the
  linear bound $H(\delta x) \ge c H(x)$ for his height $H$; the height used here is comparable to Arthur's up to powers,
  which gives the polynomial bound).
- **The maps $H_P$.** For every standard parabolic subgroup $P = M_P N_P$, with $\mathfrak{a}_P = \mathrm{Hom}(X(M_P)_k, \mathbb{R})$, the map
  $H_P \colon G(\mathbb{A}) \to \mathfrak{a}_P$ defined by $e^{\langle H_P(nmk), \chi \rangle} = \lvert \chi(m) \rvert$ for rational characters $\chi$ of $M_P$, through the
  Iwasawa decomposition $G(\mathbb{A}) = N_P(\mathbb{A}) M_P(\mathbb{A}) K$.
- **Integration on Siegel sets.** The Haar measure of a Siegel set in $G(\mathbb{A})^1$ is finite. For a non-negative
  measurable function $\varphi$ on $\mathfrak{S}^1 = \mathfrak{S} \cap G(\mathbb{A})^1$ with $\varphi(pak) \le h(a)$ for $p \in \omega$, $k \in K$ and a measurable $h$,
  $\int_{\mathfrak{S}^1} \varphi \le C \int h(a)\, \delta_{P_0}(a)^{-1}\, da$, the integral being over the norm-one slice of the cone of $a$ (the
  elements of $A_0(\mathbb{R})^0 \cap G(\mathbb{A})^1$ with $\beta(H_{P_0}(a) - T_1) > 0$ for $\beta \in \Delta_0$), for its multiplicative Haar measure,
  with $\delta_{P_0}$ the modulus character (the Jacobian of the Iwasawa decomposition) and $C$ depending on the measures
  and on $\omega$. The restriction to the norm-one slice matters: for $G = \mathbb{G}_m$ there are no roots, the
  unrestricted cone is $\mathbb{R}_{>0}$ with infinite multiplicative volume, while its norm-one slice is a point. For the unitary group $\mathrm{U}(V)$ of a Hermitian space over a CM extension $E/F$, with
  $V = V_0 \oplus \mathbb{H}^r$ and Witt index $r$, these statements take an explicit form in a Witt basis: covering
  of the quotient by a Siegel set of finite volume, the cone majorant by $\delta_{P_0}^{-1}$ (in additive coordinates, the
  factor $\prod_i t_i^{-1}$), the containment of the conjugates of the unipotent part in a fixed compact set, and the
  polynomial comparison of the height with the height of the quotient (the infimum of the heights of rational
  translates) on the Siegel set; this is the form used for the theta integrals of unitary
  groups and for the decay of their cusp forms.

## Expansion

A good expansion has pages for the definition of Siegel sets, the covering theorem, the finiteness
(Siegel) property of Siegel sets, the compactness criterion and finite volume, the finiteness of class
numbers and of conjugacy classes of parabolic subgroups, the properties of heights,
and the integration estimates, with the explicit unitary case; it should cite A. Borel, "Some finiteness
properties of adele groups over number fields", Publ. Math. IHÉS 16 (1963), 5–30 (Theorem 5.1, the finiteness
of class numbers), A. Borel and
Harish-Chandra, "Arithmetic subgroups of algebraic groups", Ann. of Math. 75 (1962), 485–535, and
A. Borel's monograph *Introduction aux groupes arithmétiques*, Hermann, 1969, with locators, besides the
sources below.

It also writes out these steps of its own proof:

- the classical proof of reduction theory, as distinct from its statement on this page: the covering of $\mathrm{GL}_n(\mathbb{R})$ by the $\mathrm{GL}_n(\mathbb{Z})$-translates of a Siegel set (Minkowski, Siegel), its transfer to $G$ through a faithful representation (Borel and Harish-Chandra), and the assembly over the finite adeles from finitely many classes, with the archimedean Iwasawa decomposition and the local decompositions above, for the covering and the finiteness statements.

## Depends on

- [Adelic norm](adeles-and-ideles/adelic-norm.md), for the normalized absolute values of the completions
- [Product formula for principal ideles](adeles-and-ideles/adelic-norm-principal-embedding.md), for the product formula on $k^\times$
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for the minimal and standard parabolic $k$-subgroups, Levi decompositions and simple roots
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the decomposition $G(k_v) = P_0(k_v) K_v$ at the finite places, through which $H_P$ is defined
- [Iwasawa and Langlands decompositions of real reductive groups](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/iwasawa-and-langlands-decompositions.md), for the Iwasawa decomposition of the real points at the archimedean places, also used to define $H_P$

## Proof depends on

- [Dirichlet's unit theorem: the logarithmic image of the units is a full lattice](../discriminants-ramification/dirichlet-unit-theorem.md), for the archimedean factor in the compactness of the norm-one idele classes, the case of $\mathrm{GL}_1$
- [Compactness of the local integral units](adeles-and-ideles/is-compact-local-integral-unit-subgroup.md), for the compact product of the local unit groups at the finite places, the other factor in that case
- [Minkowski's bound: every ideal class of a number field contains an integral ideal of small norm](../number-fields-embeddings/minkowski-bound.md), for a representative of small norm in each ideal class
- [Bound on the number of ideals of bounded norm, floor form](../discriminants-ramification/counting-ideals-of-bounded-norm/card-nonzero-abs-norm-le-real.md), for the finiteness of the ideals of bounded norm, so that with Minkowski's bound the class group of $k$ is finite: the class number for the standard maximal compact subgroup of $\mathrm{GL}_1$; an arbitrary compact open subgroup gives a finite refinement
- [Compactness of the completed ring of integers](adeles-and-ideles/is-compact-adic-completion-integers.md), for the compactness of the balls of the height, together with one finite set of places for the whole ball: the local factors of the height are at least $1$ at the finite places and take values in $q_v^{\mathbb{Z}}$, so on a ball they exceed $1$ only at places of norm bounded in terms of the radius, finitely many by the counting of ideals above, and the ball is a closed subset of a product of compact sets
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for the rational parabolic subgroups, their finitely many $G(k)$-conjugacy classes (one for each standard parabolic subgroup) and the rational Bruhat decomposition

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §2 ($G(\mathbb{A})^1$, $H_G$), §3 (the
  compactness criterion of Borel–Harish-Chandra and Mostow–Tamagawa), §8 (Siegel sets and Theorem 8.1,
  "Borel, Harish-Chandra"), §2, pp. 15–16, §3, p. 22 and §4, p. 24 (the maps $H_P$ and $\mathfrak{a}_P$ for the standard
  parabolic subgroups), §13 ((13.2)–(13.4), "See [Bor2]", for his
  height built from the Hilbert–Schmidt norm, and p. 72, the lower bound for heights of rational translates on a
  Siegel set).
- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §6 (arithmetic subgroups and the finite
  invariant measure of $\Gamma \backslash {}^\circ G$ in 6.1, Siegel sets 6.2, the theorem of 6.3 with the
  Siegel property and fundamental sets; "In the adelic case ... there is only one cusp"); the proof of
  Theorem 8.4 (finitely many $\Gamma$-conjugacy classes of maximal parabolic subgroups, "[3], 15.6").
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the unitary case for CM extensions with a non-degenerate Hermitian form in a Witt frame (covering
  and finite volume, the cone majorant by the inverse modulus, conjugation compactness and quotient-height
  control) as `GlobalTheory.Published.SiegelSetUnitary`.
