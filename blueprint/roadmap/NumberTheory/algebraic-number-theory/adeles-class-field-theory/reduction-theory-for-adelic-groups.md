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
  finite union of arithmetic quotients $\Gamma_i \backslash G_\infty$; and there are finitely many
  $G(k)$-conjugacy classes of parabolic subgroups over $k$.
- **Heights.** For the two-sided height $\lVert x \rVert = \prod_v \max_{i,j}(\lvert r(x)_{ij} \rvert_v, \lvert (r(x)^{-1})_{ij} \rvert_v)$
  defined by a faithful representation $r \colon G \to \mathrm{GL}_m$ over $k$, whose balls are compact (a height
  using only the entries of $r(x)$ need not have this property: on $\mathrm{GL}_1$ over $\mathbb{Q}$ every rational
  point would have height $1$):
  $\lVert xy \rVert \le \lVert x \rVert \lVert y \rVert$, $\lVert x^{-1} \rVert \le C_0 \lVert x \rVert^{N_0}$ and
  $\#\{\gamma \in G(k) : \lVert \gamma \rVert \le t\} \le C_0 t^{N_0}$, and the comparison of heights on a
  Siegel set with heights of their $G(k)$-translates.
- **Integration on Siegel sets.** The Haar measure of a Siegel set in $G(\mathbb{A})^1$ is finite, and an
  integral over it is bounded by an integral over the cone of $a$, for the multiplicative Haar measure of
  $A_0(\mathbb{R})^0$, against the inverse of the modulus character $\delta_{P_0}$ (the Jacobian of the Iwasawa
  decomposition). For the unitary group $\mathrm{U}(V)$ of a Hermitian space over a CM extension $E/F$, with
  $V = V_0 \oplus \mathbb{H}^r$ and Witt index $r$, these statements take an explicit form in a Witt basis: covering
  of the quotient by a Siegel set of finite volume, the cone majorant by $\delta_{P_0}^{-1}$, the compactness of the
  conjugates of the unipotent part, and the control of the height of the quotient (the infimum of the heights
  of rational translates) on the Siegel set; this is the form used for the theta integrals of unitary
  groups and for the decay of their cusp forms.

A good expansion has pages for the definition of Siegel sets, the covering theorem, the finiteness
(Siegel) property of Siegel sets, the compactness criterion and finite volume, the finiteness of class
numbers and of conjugacy classes of parabolic subgroups, the properties of heights,
and the integration estimates, with the explicit unitary case; it should cite A. Borel, "Some finiteness
properties of adele groups over number fields", Publ. Math. IHÉS 16 (1963), 5–30 (Theorem 5.1, the finiteness
of class numbers), A. Borel and
Harish-Chandra, "Arithmetic subgroups of algebraic groups", Ann. of Math. 75 (1962), 485–535, and
A. Borel's monograph *Introduction aux groupes arithmétiques*, Hermann, 1969, with locators, besides the
sources below.

## Depends on

- [Adelic norm](adeles-and-ideles/adelic-norm.md), for the normalized absolute values of the completions
- [Product formula for principal ideles](adeles-and-ideles/adelic-norm-principal-embedding.md), for the product formula on $k^\times$

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §2 ($G(\mathbb{A})^1$, $H_G$), §3 (the
  compactness criterion of Borel–Harish-Chandra and Mostow–Tamagawa), §8 (Siegel sets and Theorem 8.1,
  "Borel, Harish-Chandra"), §13 ((13.2)–(13.4), "See [Bor2]").
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
