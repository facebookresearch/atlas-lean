# Inertia and tame inertia of a p-adic field

Let $K$ be a finite extension of $\mathbb{Q}_p$ with residue field $k$ of $q$ elements, $\bar K$ an algebraic
closure with residue field $\bar k$, and $K^{\mathrm{ur}} \subseteq K^{\mathrm{tame}} \subseteq \bar K$ the
maximal unramified and the maximal tamely ramified extensions of $K$. The **inertia group**
$I_K = \operatorname{Gal}(\bar K/K^{\mathrm{ur}})$ and the **wild inertia group**
$P_K = \operatorname{Gal}(\bar K/K^{\mathrm{tame}})$ are closed normal subgroups of $G_K$, and
$G_K / I_K = \operatorname{Gal}(K^{\mathrm{ur}}/K) \cong \operatorname{Gal}(\bar k/k) \cong \hat{\mathbb{Z}}$, generated
by the arithmetic Frobenius $x \mapsto x^q$. The group $P_K$ is a pro-$p$ group, and there is a canonical
isomorphism

$$I_K / P_K \xrightarrow{\ \sim\ } \varprojlim_{(N, p) = 1} \mu_N(\bar k) = \prod_{\ell \ne p} T_\ell(\mu(\bar k)),
\qquad T_\ell(\mu(\bar k)) = \varprojlim_n \mu_{\ell^n}(\bar k),$$

the first limit being over the integers $N$ prime to $p$ ordered by divisibility, and $T_\ell(\mu(\bar k))$ the
Tate module of the roots of unity of $\bar k$, which Fontaine–Ouyang write $\mathbb{Z}_\ell(1)$. Under it, the action
of $G_K/I_K = \operatorname{Gal}(\bar k/k)$ on $I_K/P_K$ by conjugation is its natural action on the roots of unity, so
that $g \tau g^{-1} = \tau^{\chi_\ell(g)}$ for $\tau$ in the $\ell$-component, with $\chi_\ell$ the $\ell$-adic cyclotomic
character. A choice of compatible primitive $\ell^n$-th roots of unity of $\bar k$ identifies $T_\ell(\mu(\bar k))$ with
the scalar twist $\mathbb{Z}_\ell(1)$, an identification that is not canonical. For a prime $\ell \ne p$, let
$P_{K,\ell} \subseteq I_K$ be the inverse image of $\prod_{\ell' \ne p, \ell} T_{\ell'}(\mu(\bar k))$ and
$G_{K,\ell} = G_K / P_{K,\ell}$; then $I_K / P_{K,\ell} \cong T_\ell(\mu(\bar k))$ canonically, and there is an exact
sequence $1 \to T_\ell(\mu(\bar k)) \to G_{K,\ell} \to \operatorname{Gal}(\bar k/k) \to 1$.

## Depends on

- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for $\chi_\ell$ and the scalar twist $\mathbb{Z}_\ell(1)$

## Proof depends on

- [Ramification groups of local fields](../../discriminants-ramification/ramification-groups-of-local-fields.md), for the injection of $G_0/G_1$ into the multiplicative group of the residue field and the fact that $G_1$ is a $p$-group, in each finite Galois extension

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §1.3.2 (the definitions of $K^{\mathrm{ur}}$, $K^{\mathrm{tame}}$, $I_K$ and $P_K$, and the canonical isomorphism of
  $I_K/P_K$ with $\varprojlim_N \mu_N(\bar k)$ through the diagram (1.35)) and Proposition 1.66 ("If write
  $\mathbb{Z}_\ell(1) = \varprojlim_n \mu_{\ell^n}$ … then $I_K/P_K \cong \prod_{\ell \ne p} \mathbb{Z}_\ell(1)$ canonically", with the
  conjugation action of $G_k$ the natural action); §2.3.1, the definitions of
  $P_{K,\ell}$ and $G_{K,\ell}$ and the exact sequence (2.18), and the relation $g t g^{-1} = t^{\chi_\ell(g)}$
  in the proof of Theorem 2.26.
- J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979: Chapter IV, §§1–2
  (ramification groups and the structure of the tame quotient), cited by Fontaine–Ouyang.
