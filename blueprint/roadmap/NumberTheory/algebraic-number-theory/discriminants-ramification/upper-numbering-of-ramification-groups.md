# Upper numbering of ramification groups

This node is still to be broken down. It covers Herbrand's functions, the ramification groups in the upper
numbering of a finite Galois extension of local fields, Herbrand's theorem, and the upper-numbering filtration
of the Galois group of an infinite Galois extension, in particular of the absolute Galois group of a $p$-adic
field.

Here a local field is a field complete for a discrete valuation, with perfect residue field of characteristic
$p > 0$. Let $L/K$ be a finite Galois extension of local fields, $G = \operatorname{Gal}(L/K)$, and $G_i$
($i \ge -1$ an integer) its ramification groups in the lower numbering, as in
[Ramification groups of local fields](ramification-groups-of-local-fields.md). For a real number $u \ge -1$ put
$G_u = G_i$, where $i$ is the smallest integer $\ge u$, and

$$\varphi_{L/K}(u) = \int_0^u \frac{dt}{(G_0 : G_t)},$$

where $(G_0 : G_t)$ is read as $(G_{-1} : G_0)^{-1}$ for $t = -1$ and as $1$ for $-1 < t \le 0$, so that
$\varphi_{L/K}(u) = u$ for $-1 \le u \le 0$. The function $\varphi_{L/K}$ is a continuous, piecewise linear,
increasing and concave homeomorphism of $[-1, \infty)$ onto itself; write $\psi_{L/K}$ for its inverse. The
**ramification groups in the upper numbering** are

$$G^v = G_{\psi_{L/K}(v)} \qquad (v \ge -1),$$

so that $G^{-1} = G$, $G^0 = G_0$ and $G^v = 1$ for all large $v$. **Herbrand's theorem** says that for a
Galois subextension $K'/K$ with $H = \operatorname{Gal}(L/K')$ one has $G_u H / H = (G/H)_{\varphi_{L/K'}(u)}$,
and hence, with the transitivity $\psi_{L/K} = \psi_{L/K'} \circ \psi_{K'/K}$, $G^v H / H = (G/H)^v$ for
every $v \ge -1$.

For an infinite algebraic Galois extension $L$ of a local field $K$, with group $G$ ($L$ itself need not be
complete or discretely valued), the
**ramification groups in the upper numbering** are

$$G^v = \varprojlim_{L'} \operatorname{Gal}(L'/K)^v \qquad (v \ge -1),$$

the limit over the finite Galois extensions $L'/K$ inside $L$, along the maps that Herbrand's theorem makes
surjective. They form a decreasing filtration of $G$ by closed normal subgroups that is left continuous,
$G^v = \bigcap_{w < v} G^w$, with $\bigcap_{v} G^v = 1$, since each $\operatorname{Gal}(L'/K)^v$ is trivial for
large $v$, and $(G/H)^v = G^v H/H$ for every closed normal subgroup $H$. For a finite extension $K$ of
$\mathbb{Q}_p$ and $L = \overline{K}$ this gives the filtration $(G_K^v)_{v \ge -1}$ of the absolute Galois group
$G_K$, with $G_K^v$ equal to the inertia group $I_K$ for $-1 < v \le 0$ and contained in the wild inertia group
$P_K$ for $v > 0$: at each finite level $\operatorname{Gal}(L'/K)^v$ lies in $G_1$, the image of $P_K$, for
$v > 0$.

## Expansion

A good expansion states and links:

1. the functions $\varphi_{L/K}$ and $\psi_{L/K}$ of a finite Galois extension: the function $i_G$ of a
   quotient (Fontaine–Ouyang, Proposition 1.68), the properties of $\varphi_{L/K}$ (Proposition 1.69), the formula
   $\varphi_{L/K}(u) = \frac{1}{|G_0|} \sum_{s \in G} \min\{i_G(s), u + 1\} - 1$ with
   $i_G(s) = v_L(s(x) - x)$ for a generator $x$ of $\mathcal{O}_L$ over $\mathcal{O}_K$ (Proposition 1.70), the
   formula $\psi_{L/K}(v) = \int_0^v (G^0 : G^w)\,dw$ ((1.44)) and the transitivity
   $\varphi_{L/K} = \varphi_{K'/K} \circ \varphi_{L/K'}$, $\psi_{L/K} = \psi_{L/K'} \circ \psi_{K'/K}$
   (Proposition 1.72);
2. Herbrand's theorem (Theorem 1.71) and the compatibility of the upper numbering with quotients
   (Proposition 1.73);
3. the upper numbering of an infinite Galois extension ((1.45)), its left continuity, and its behaviour under
   open normal subgroups and under quotients by closed normal subgroups (Proposition 1.74);
4. the filtration $(G_K^v)$ of the absolute Galois group of a finite extension $K$ of $\mathbb{Q}_p$: that
   $G_K^v = I_K$ for $-1 < v \le 0$, that $\bigcap_v G_K^v = 1$, that $G_K^v \subseteq P_K$ for $v > 0$, and that
   the union of the groups $G_K^v$ for $v > 0$ is dense in $P_K$, its image in each finite quotient being the
   image of $P_K$; Darmon, Diamond and Taylor list these properties for $K = \mathbb{Q}_p$, printing
   $P_p = \bigcup_{u > 0} I_p^u$.

## Depends on

- [Ramification groups of local fields](ramification-groups-of-local-fields.md), for the lower-numbering groups $G_i$
- [Inertia and tame inertia of a p-adic field](../galois-representations/weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for the inertia group $I_K$ and the wild inertia group $P_K$

## Proof depends on

- [Ramification groups of local fields](ramification-groups-of-local-fields.md), for $H_i = G_i \cap H$ for a subgroup $H$ (Fontaine–Ouyang, Proposition 1.67), used in the proof of Herbrand's theorem, and for $G_1$ being a normal $p$-subgroup of $G_0$ of index prime to $p$, which makes $G_1$ the image of the wild inertia group
- [Monogenicity of extensions with separable residue field extension](../../../RingTheory/ramification/monogenic-extensions-of-discrete-valuation-rings/exists-adjoin-eq-top-of-separable-residu.md), for a generator $x$ of $\mathcal{O}_L$ as an $\mathcal{O}_K$-algebra, which defines $i_G$ and is used, with one of $\mathcal{O}_{K'}$ over $\mathcal{O}_K$, in the proof of Proposition 1.68: $\mathcal{O}_L$ is a finite $\mathcal{O}_K$-module with local structure map, and the residue extension is separable because the residue field of $K$ is perfect

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §1.1, Definition 1.16, p. 7 (local fields); §1.3.1, p. 22 ("We fix an element $x$ of $\mathcal{O}_L$ which
  generates $\mathcal{O}_L$ as an $\mathcal{O}_K$-algebra (such an $x$ exists by $p$-adic analysis)"); §1.3.3, pp. 25–28 (the function $i_G$ (1.37), Proposition 1.68, $G_u$ and $\Phi = \varphi_{L/K}$ (1.39),
  Propositions 1.69 and 1.70, Herbrand's Theorem 1.71, $\Psi = \psi_{L/K}$, Proposition 1.72, the upper numbering (1.43) with
  $G^{-1} = G$, $G^0 = G_0$ and $G^v = 1$ for $v \gg 0$, the formula (1.44) and Proposition 1.73), and §1.3.4,
  pp. 28–29 (the upper numbering (1.45) of an infinite Galois extension, its left continuity, and
  Proposition 1.74).
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", in *Current Developments in Mathematics, 1995*,
  International Press, Cambridge, MA, 1995; page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §2.1, pp. 50–51 (the closed
  normal subgroups $I_p^u$ of $G_{\mathbb{Q}_p}$ for $u \in [-1, \infty]$: decreasing, $I_p^u = I_p$ for
  $u \le 0$, $I_p^\infty = \{1\}$, $P_p = \bigcup_{u > 0} I_p^u$, $I_p^u = \bigcap_{v < u} I_p^v$, "defined in
  section 3 of chapter IV of [Se2], where they are denoted $G^u_{\mathbb{Q}_p}$ (except that there,
  $G^{-1}_{\mathbb{Q}_p} = G_{\mathbb{Q}_p}$ whereas we have $I_p^{-1} = I_p$)").
- J.-P. Serre, *Corps locaux*, Hermann, Paris, 1962: Chapter IV, §3, the definition cited by Darmon, Diamond and
  Taylor.
