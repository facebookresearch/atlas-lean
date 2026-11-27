# Prismatic F-crystals and lattices in crystalline representations

Let $K$ be a complete discretely valued field of mixed characteristic $(0, p)$ with perfect residue field, for
instance a finite extension of $\mathbb{Q}_p$, with ring of integers $\mathcal{O}_K$. A **prismatic $F$-crystal** (of
vector bundles) on $\operatorname{Spf}(\mathcal{O}_K)$ is a pair $(\mathcal{E}, \varphi_{\mathcal{E}})$ of a vector bundle
$\mathcal{E}$ on the absolute prismatic site $(\operatorname{Spf}(\mathcal{O}_K)_\Delta, \mathcal{O}_\Delta)$ and an isomorphism
$\varphi_{\mathcal{E}} \colon (\varphi^* \mathcal{E})[1/I_\Delta] \cong \mathcal{E}[1/I_\Delta]$. The étale realization
functor gives an equivalence of categories

$$T_{\mathcal{O}_K} \colon \operatorname{Vect}^{\varphi}(\operatorname{Spf}(\mathcal{O}_K)_\Delta, \mathcal{O}_\Delta) \xrightarrow{\ \sim\ }
\operatorname{Rep}^{\mathrm{crys}}_{\mathbb{Z}_p}(G_K)$$

onto the category of finite free $\mathbb{Z}_p$-modules $T$ with a continuous action of $G_K$ such that $T[1/p]$ is
a crystalline representation; in particular every $G_K$-stable lattice in a crystalline representation comes
from a prismatic $F$-crystal, unique up to unique isomorphism, and morphisms of lattices correspond to morphisms
of $F$-crystals. As the equivalence is $\mathbb{Z}_p$-linear on morphisms, the same holds for lattices with
coefficients: if $L$ is a finite extension of $\mathbb{Q}_p$ and $T$ is a $G_K$-stable $\mathcal{O}_L$-lattice in a
crystalline representation on an $L$-vector space, the action of $\mathcal{O}_L$ on $T$ by $G_K$-equivariant
endomorphisms corresponds to an action of $\mathcal{O}_L$ on the prismatic $F$-crystal of $T$.

## Depends on

- [Absolute prismatic site and prismatic F-crystals](absolute-prismatic-site-and-prismatic-f-crystals.md), for the absolute prismatic site, $\mathcal{O}_\Delta$, $I_\Delta$, $\varphi$, prismatic $F$-crystals and the étale realization (its item 2)
- [Crystalline representations](crystalline-representations.md)

## Proof depends on

- [Absolute prismatic site and prismatic F-crystals](absolute-prismatic-site-and-prismatic-f-crystals.md), for the prismatic and quasi-syntomic sites, prismatic $F$-crystals and their realizations (its items 1 and 2), Fargues's description of the $F$-crystals over $\mathcal{O}_C$ (its item 3) and the descent machinery of Bhatt–Scholze 2021, §§6.1–6.3 (its item 4), from which this classification is proved: full faithfulness in §5 (Proposition 5.3, Construction 5.5), which uses only the fully faithful direction of Fargues's description (Theorem 5.2 and the end of Construction 5.5), and essential surjectivity in §6.4, an $A_{\mathrm{inf}}$-variant of Kisin's argument that rests on Kedlaya's slope filtrations through Berger's observation (§1.1 and §6.4, n. 12), by descent along $\operatorname{Spf}(\mathcal{O}_C) \to \operatorname{Spf}(\mathcal{O}_K)$
- [de Rham representations](de-rham-representations.md), for the comparison $V \otimes_{\mathbb{Q}_p} B_{\mathrm{dR}} \cong D_{\mathrm{dR}}(V) \otimes_K B_{\mathrm{dR}}$ of a de Rham, here crystalline, representation $V$ in Construction 5.5
- [Weakly admissible implies admissible](colmez-fontaine-theorem.md), for Fontaine's theorem that the filtered $\varphi$-module $D_{\mathrm{cris}}(T[1/p])$ of the given crystalline representation is weakly admissible, the input of the proof of essential surjectivity (Bhatt–Scholze 2021, §6.4); that page is stated for the same fields $K$, complete and discretely valued of characteristic $0$ with perfect residue field
- [p-divisible groups over the ring of integers of C](p-divisible-groups-over-o-c.md), for the vector bundles on the Fargues–Fontaine curve used in §6.4

## Sources

- B. Bhatt and P. Scholze, "Prismatic F-crystals and crystalline Galois representations", Cambridge J. Math.
  11 (2023), 507–562, arXiv:2106.14735 (version 2): Abstract, Definition 1.1 (= Definition 4.1), Theorem 1.2
  (= Theorem 5.6) and the outline of its proof in §1.1.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the essential surjectivity and full faithfulness, for lattices in crystalline representations and for
  their lattices of coefficients, as `GlobalTheory.Published.BhattScholzeIntegral` and
  `GlobalTheory.Published.BhattScholzeCrystallineLattices`.
