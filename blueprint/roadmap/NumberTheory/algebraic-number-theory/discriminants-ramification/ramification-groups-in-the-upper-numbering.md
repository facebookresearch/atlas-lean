# Upper numbering of ramification groups

Here a local field is a field complete for a discrete valuation, with perfect residue field of characteristic
$p > 0$. Let $L/K$ be a finite Galois extension of local fields, $G = \operatorname{Gal}(L/K)$, $G_u$ ($u \ge -1$
real) its ramification groups in the lower numbering, and $\psi_{L/K}$ the inverse of Herbrand's function
$\varphi_{L/K}$, as in [Herbrand's functions](upper-numbering-of-ramification-groups-results/herbrand-functions.md). The
**ramification groups in the upper numbering** are

$$G^v = G_{\psi_{L/K}(v)} \qquad (v \ge -1),$$

equivalently $G^{\varphi_{L/K}(u)} = G_u$. They form a decreasing filtration of $G$ by normal subgroups, with
$G^{-1} = G$, $G^0 = G_0$, the inertia group, and $G^v = 1$ for all large $v$; it is left continuous,
$G^v = \bigcap_{w < v} G^w$, and $\psi_{L/K}(v) = \int_0^v (G^0 : G^w)\,dw$. For a normal subgroup $H$ of $G$
with fixed field $K'$, the upper numbering of $G/H = \operatorname{Gal}(K'/K)$ is the image of that of $G$:

$$(G/H)^v = G^v H / H \qquad (v \ge -1).$$

The group $H = \operatorname{Gal}(L/K')$ has its own upper numbering, for the extension $L/K'$, and

$$G^v \cap H = H^{\psi_{K'/K}(v)} \qquad (v \ge -1),$$

since $G^v \cap H = G_{\psi_{L/K}(v)} \cap H$ is the lower-numbering group $H_{\psi_{L/K}(v)}$ of $L/K'$, and
$\varphi_{L/K'} \circ \psi_{L/K} = \psi_{K'/K}$.

For an infinite algebraic Galois extension $L$ of a local field $K$, with group $G$ ($L$ itself need not be
complete or discretely valued), the **ramification groups in the upper numbering** are

$$G^v = \varprojlim_{L'} \operatorname{Gal}(L'/K)^v \qquad (v \ge -1),$$

the limit over the finite Galois extensions $L'/K$ inside $L$ along the restriction maps, which map
$\operatorname{Gal}(L''/K)^v$ onto $\operatorname{Gal}(L'/K)^v$ for $L' \subseteq L''$ by the compatibility with
quotients. They form a decreasing filtration of $G$ by closed normal subgroups that is left continuous,
$G^v = \bigcap_{w < v} G^w$, with $\bigcap_{v} G^v = 1$, since each $\operatorname{Gal}(L'/K)^v$ is trivial for
large $v$, and $(G/H)^v = G^v H/H$ for every closed normal subgroup $H$. If $H$ is an open normal subgroup of
$G$, with fixed field $K'$, a finite Galois extension of $K$, then $H = \operatorname{Gal}(L/K')$ has its own upper
numbering, for $L/K'$, and $G^v \cap H = H^{\psi_{K'/K}(v)}$ for $v \ge -1$: the finite Galois extensions $L''/K$ inside
$L$ that contain $K'$ are cofinal among the finite Galois extensions of $K$ and of $K'$ inside $L$, and the formula
for $\operatorname{Gal}(L''/K)$ and its normal subgroup $\operatorname{Gal}(L''/K')$ passes to the inverse limit.
For a finite extension $K$ of
$\mathbb{Q}_p$ and $L = \overline{K}$ this gives the filtration $(G_K^v)_{v \ge -1}$ of the absolute Galois group
$G_K$, with $G_K^v$ equal to the inertia group $I_K$ for $-1 < v \le 0$ and contained in the wild inertia group
$P_K$ for $v > 0$: at each finite level $\operatorname{Gal}(L'/K)^v$ lies in $G_1$, the image of $P_K$, for
$v > 0$. Moreover $P_K$ is the closure of the subgroup $\bigcup_{v > 0} G_K^v$: at each finite level
$\operatorname{Gal}(L'/K)^v = G_1$ for $0 < v \le \varphi_{L'/K}(1)$, since then $0 < \psi_{L'/K}(v) \le 1$, and $G_K^v$
maps onto $\operatorname{Gal}(L'/K)^v$, the restriction maps of the inverse limit being surjective; so the union and
the closed subgroup $P_K$ that contains it have the same image in every finite quotient of $G_K$, hence the same
closure. For $K = \mathbb{Q}_p$, Darmon, Diamond and Taylor write $P_p = \bigcup_{u > 0} I_p^u$.

## Depends on

- [Herbrand's functions](upper-numbering-of-ramification-groups-results/herbrand-functions.md), for the groups $G_u$ and the functions $\varphi_{L/K}$ and $\psi_{L/K}$
- [Ramification groups of local fields](ramification-groups-of-local-fields.md), for the lower-numbering groups $G_i$ and the inertia group $G_0$
- [Inertia and tame inertia of a p-adic field](../galois-representations/weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for the inertia group $I_K$ and the wild inertia group $P_K$

## Proof depends on

- [Herbrand's functions](upper-numbering-of-ramification-groups-results/herbrand-functions.md), for $\psi_{L/K}$ being an increasing homeomorphism of $[-1, +\infty)$ onto itself with $\psi_{L/K}(v) = v$ for $-1 \le v \le 0$ and derivative $(G_0 : G_{\psi_{L/K}(v)})$ away from finitely many points, which give $G^{-1} = G$, $G^0 = G_0$, $G^v = 1$ for large $v$, the left continuity of $v \mapsto G^v$, inherited from that of $u \mapsto G_u$, the integral formula for $\psi_{L/K}$, and $G^v = G_1$ for $0 < v \le \varphi_{L/K}(1)$, where $0 < \psi_{L/K}(v) \le 1$
- [Herbrand's theorem](upper-numbering-of-ramification-groups-results/herbrand-s-theorem.md), for $(G/H)_x = G_w H/H$ with $w = \psi_{L/K'}(x)$, and [Transitivity of Herbrand's functions](upper-numbering-of-ramification-groups-results/transitivity-of-herbrand-functions.md), for $\psi_{L/K'}(\psi_{K'/K}(v)) = \psi_{L/K}(v)$: with $x = \psi_{K'/K}(v)$ they give $(G/H)^v = (G/H)_x = G^v H/H$, hence the surjectivity of the restriction maps between finite levels and the compatibility with quotients by closed normal subgroups in the infinite case; the transitivity also gives $\varphi_{L/K'} \circ \psi_{L/K} = \psi_{K'/K}$, for $G^v \cap H = H^{\psi_{K'/K}(v)}$
- [Ramification groups of local fields](ramification-groups-of-local-fields.md), for $H_u = G_u \cap H$ for a subgroup $H$ of $G$, which gives $G^v \cap H = H_{\psi_{L/K}(v)}$, for $G_0$ being the inertia group, for $G_i \subseteq G_1$ when $i \ge 1$, and for $G_1$ being a normal $p$-subgroup of $G_0$ of index prime to $p$, which makes $G_1$ the image of the wild inertia group
- [Inertia and tame inertia of a p-adic field](../galois-representations/weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for $I_K$, whose image in each $\operatorname{Gal}(L'/K)$ is the inertia group $G_0$ of $L'/K$, and for $P_K$ being a closed normal pro-$p$ subgroup of $I_K$ with $I_K/P_K$ a product of groups $T_\ell(\mu(\bar k))$, $\ell \ne p$, so that the image of $P_K$ is the $p$-subgroup $G_1$ of $G_0$

## Sources

- J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter IV, where the residue
  extensions are only assumed separable:
  - §1, Proposition 1, p. 62 ("$G_0$ is the inertia subgroup of $G$"), and Proposition 2, p. 62 ("For every
    $s \in H$, $i_H(s) = i_G(s)$, and $H_i = G_i \cap H$", for a subgroup $H$ of $G$);
  - §2, proof of Corollary 4 to Proposition 7, p. 68 ("By corollaries 1 and 3, $G_1$ is a $p$-group and
    $G_0/G_1$ is cyclic of order prime to $p$");
  - §3, p. 74: the upper numbering $G^v = G_{\psi(v)}$, "or, equivalently, $G^{\varphi(u)} = G_u$", "We have
    $G^{-1} = G$, $G^0 = G_0$, and $G^v = \{1\}$ for $v$ sufficiently large", $\psi(v) = \int_0^v (G^0 : G^w)\,dw$,
    and Proposition 14 ("If $H$ is a normal subgroup of $G$, then $(G/H)^v = G^vH/H$ for all $v$"), with its proof,
    p. 75, and Proposition 15, p. 74 (the transitivity formulas $\varphi_{L/K} = \varphi_{K'/K} \circ \varphi_{L/K'}$ and
    $\psi_{L/K} = \psi_{L/K'} \circ \psi_{K'/K}$);
  - §3, p. 75, Remark 1: "Let $L/K$ be an infinite Galois extension, $G$ its Galois group. One can define $G^v$
    as $\varprojlim G(L'/K)^v$, $L'$ running through the set of finite Galois subextensions of $L$. The $G^v$
    again form a filtration of $G$; this filtration is *left continuous*: $G^v = \bigcap_{w<v} G^w$."
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  at <http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §1.3.4, Proposition 1.74, p. 29: for an infinite Galois extension $L/K$ with group $G$ and a closed normal
  subgroup $H$ with fixed field $L'$, "(1) If $H$ is also open in $G$, then $G^v \cap H = H^{\psi_{G/H}(v)}$ where
  $\Psi_{G/H} := \Psi_{L'/K}$", proved from the finite-level formula $(G/N)^v \cap H/N = (H/N)^{\Psi_{G/H}(v)}$ by passing to
  the limit, and "(2) In general, $(G/H)^v = G^vH/H$".
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", in *Current Developments in Mathematics, 1995*,
  International Press, Cambridge, MA, 1995; page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §2.1, pp. 50–51 (the closed
  normal subgroups $I_p^u$ of $G_{\mathbb{Q}_p}$ for $u \in [-1, \infty]$: decreasing, $I_p^u = I_p$ for
  $u \le 0$, $I_p^\infty = \{1\}$, $P_p = \bigcup_{u > 0} I_p^u$, $I_p^u = \bigcap_{v < u} I_p^v$, "defined in
  section 3 of chapter IV of [Se2], where they are denoted $G^u_{\mathbb{Q}_p}$ (except that there,
  $G^{-1}_{\mathbb{Q}_p} = G_{\mathbb{Q}_p}$ whereas we have $I_p^{-1} = I_p$)").
