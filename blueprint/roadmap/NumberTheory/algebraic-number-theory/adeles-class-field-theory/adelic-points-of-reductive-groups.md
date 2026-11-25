# Adelic points of reductive groups: the norm-one subgroup and maximal compact subgroups

This node is still to be broken down. It covers the structure of the adelic points of a reductive group that the
automorphic pages use beside reduction theory. Let $k$ be a number field, $\mathbf{G}$ a connected reductive group over
$k$, $\mathbf{P} = \mathbf{M}\mathbf{N}$ a parabolic $k$-subgroup with Levi factor $\mathbf{M}$, and $G(\mathbb{A})^1$,
$A_G$ and $H_G$ as in [reduction theory](reduction-theory-for-adelic-groups.md).

- **The norm-one subgroup.** Here $A_G$ is the maximal $\mathbb{Q}$-split torus in the centre of the restriction of
  scalars of $\mathbf{G}$ to $\mathbb{Q}$, embedded in $G(\mathbb{A})$ through the archimedean places. $G(\mathbb{A})$ is the
  direct product of $G(\mathbb{A})^1$ and $A_G(\mathbb{R})^0$, and $H_G$ restricts to an isomorphism of $A_G(\mathbb{R})^0$ onto
  $\mathfrak{a}_G$; likewise $M(\mathbb{A}) = M(\mathbb{A})^1 \times A_M(\mathbb{R})^0$.
- **Good maximal compact subgroups.** At each finite place $v$ where $\mathbf{G}$ is unramified, so at almost all finite
  places, $G(k_v)$ has hyperspecial maximal compact subgroups, and there is a maximal compact subgroup
  $K = \prod_v K_v$ of $G(\mathbb{A})$, hyperspecial at almost all finite places, with $G(\mathbb{A}) = P(\mathbb{A})K$; then
  $G(\mathbb{A}) = N(\mathbb{A}) M(\mathbb{A})^1 A_M(\mathbb{R})^0 K$.
- **Finiteness.** For every maximal compact subgroup $K$ of $G(\mathbb{A})$ the double coset space
  $P(\mathbb{A}) \backslash G(\mathbb{A}) / K$ is finite.

## Expansion

A good expansion has statement pages for the decomposition $G(\mathbb{A}) = G(\mathbb{A})^1 \times A_G(\mathbb{R})^0$, for the
existence of maximal compact subgroups in good position, hyperspecial at the unramified finite places, and for the
finiteness of $P(\mathbb{A}) \backslash G(\mathbb{A}) / K$, each citing the sources below with locators. The finiteness
reduces to a product over the places: the archimedean factor is a single double coset by the real Iwasawa
decomposition, almost all non-archimedean factors are single double cosets because $K_v$ is good there, and each
remaining factor $P(k_v) \backslash G(k_v) / K_v$ is finite since $P(k_v) \backslash G(k_v)$ is compact and $K_v$ open.

## Depends on

- [Siegel sets and reduction theory for adelic groups](reduction-theory-for-adelic-groups.md), for $G(\mathbb{A})^1$, $A_G$ and $H_G$
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](../../../GroupTheory/linear-groups/parabolic-subgroups-and-rational-bruhat-decomposition.md), for parabolic
  $k$-subgroups and Levi factors

## Proof depends on

- [Iwasawa and Langlands decompositions of real reductive groups](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/iwasawa-and-langlands-decompositions.md), for the archimedean places
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for special and hyperspecial maximal
  compact subgroups at the non-archimedean places

## Sources

- J. Arthur, "An introduction to the trace formula", in *Harmonic Analysis, the Trace Formula, and
  Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 1–263,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §3, p. 16 ($A_G$, $\mathfrak{a}_G$, $H_G$, and $G(\mathbb{A})$ as the direct product of $G(\mathbb{A})^1$ and
  $A_G(\mathbb{R})^0$), §4, p. 24 ($K = \prod_v K_v$ with $G(\mathbb{A}) = P_0(\mathbb{A})K$, citing Tits, (3.3.2) and (3.9);
  $G(\mathbb{A}) = N_P(\mathbb{A}) M_P(\mathbb{A})^1 A_P(\mathbb{R})^0 K$), and §26, p. 181 (at a place where $G$ is unramified, a
  hyperspecial maximal compact subgroup $K_v$ in the apartment of a maximal torus, after Tits).
- R. P. Langlands, "On the notion of an automorphic representation", Proc. Sympos. Pure Math. 33, Part 1, 1979,
  203–207, <https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/notion-ps.pdf>: pp. 3–4 (coset
  representatives $\{g_i\}$ for $P(\mathbb{A}) \backslash G(\mathbb{A}) / K$, finitely many, for a maximal compact $K$).
- J. Tits, "Reductive groups over local fields", Proc. Sympos. Pure Math. 33, Part 1, 1979, 29–69, §3, as cited by
  Arthur.
