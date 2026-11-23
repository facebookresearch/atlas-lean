# Weil group of a p-adic field

Let $K$ be a finite extension of $\mathbb{Q}_p$ with residue field $k$ of $q$ elements, inertia group
$I_K \subseteq G_K$ and $\pi \colon G_K \to G_K/I_K \cong \operatorname{Gal}(\bar k/k)$. Let
$\mathrm{Frob}_K \in \operatorname{Gal}(\bar k/k)$ be the **geometric Frobenius**, the inverse of
$x \mapsto x^q$. The **Weil group** $W_K$ is the inverse image $\pi^{-1}(\mathrm{Frob}_K^{\mathbb{Z}})$; it sits in
an exact sequence $1 \to I_K \to W_K \to \mathbb{Z} \to 1$, where $w \in W_K$ maps to the integer $m$ with
$\pi(w) = \mathrm{Frob}_K^m$. It carries the unique topology of a locally compact group for which $I_K$, with its
profinite topology, is an open subgroup; with it the inclusion $W_K \subseteq G_K$ is continuous with dense
image (but not a homeomorphism onto its image). For a finite extension $L/K$ in $\bar K$, $W_L = W_K \cap G_L$
is an open subgroup of finite index.

Local class field theory gives an isomorphism of topological groups

$$\mathrm{Art}_K \colon K^\times \xrightarrow{\ \sim\ } W_K^{\mathrm{ab}}$$

onto the maximal abelian Hausdorff quotient of $W_K$, which maps $\mathcal{O}_K^\times$ onto the image of $I_K$
and every uniformizer to a lift of the geometric Frobenius. In terms of the local Artin map
$\mathrm{rec}_K \colon K^\times \to \operatorname{Gal}(K^{\mathrm{ab}}/K)$ of local class field theory, normalized
so that uniformizers act on $K^{\mathrm{ur}}$ as the arithmetic Frobenius, $\mathrm{Art}_K(x) = \mathrm{rec}_K(x)^{-1}$,
with $W_K^{\mathrm{ab}}$ identified with its image in $\operatorname{Gal}(K^{\mathrm{ab}}/K)$. For $w \in W_K$ write
$\lvert w \rvert = \lvert \mathrm{Art}_K^{-1}(w) \rvert_K$, with $\lvert x \rvert_K = q^{-v_K(x)}$; thus
$\lvert w \rvert = q^{-m}$ when $\pi(w) = \mathrm{Frob}_K^m$.

## Depends on

- [Inertia and tame inertia of a p-adic field](inertia-and-tame-inertia-of-a-p-adic-field.md), for $I_K$ and $G_K/I_K \cong \operatorname{Gal}(\bar k/k)$
- [Local class field theory: the local Artin map](../../../p-adic-numbers/local-class-field-theory.md), for $\mathrm{rec}_K$, of which $\mathrm{Art}_K$ is the reciprocal

## Proof depends on

- [Local class field theory: the local Artin map](../../../p-adic-numbers/local-class-field-theory.md), for the isomorphism $K^\times \cong W_K^{\mathrm{ab}}$, through the Weil groups $W(L/K)$ of the local fundamental classes
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the local fundamental classes defining the groups $W(L/K)$ (its item 3)

## Sources

- R. Taylor and T. Yoshida, "Compatibility of local and global Langlands correspondences", J. Amer. Math.
  Soc. 20 (2007), 467–493, arXiv:math/0412357 (version 2), §1, pp. 2–3 (the geometric Frobenius
  $\mathrm{Frob}_{v_K}$, $W_K$ as the preimage of $\mathrm{Frob}_{v_K}^{\mathbb{Z}}$ with $I_K$ open, and
  $\mathrm{Art}_K \colon K^\times \cong W_K^{\mathrm{ab}}$ taking uniformisers to lifts of $\mathrm{Frob}_{v_K}$).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", arXiv:math/0011210
  (version 2): (1.1.5)–(1.1.8) (the Artin reciprocity homomorphism, its characterization, inertia and the Weil
  group with its topology), (1.1.9) (the Weil group as the limit of the $W(L/K)$), (1.1.10)
  ($\mathrm{Art}_K \colon K^\times \cong W_K^{\mathrm{ab}}$, mapping $\mathcal{O}_K^\times$ onto $I_K^{\mathrm{ab}}$ and a
  uniformizer to a geometric Frobenius element), (3.1.2) ($\lvert w \rvert$), (3.1.5) ($W_L \to W_K$).
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §2.3.3, Definition 2.32 (the Weil group, defined with the arithmetic Frobenius $\tau_k$, which generates the
  same subgroup).
