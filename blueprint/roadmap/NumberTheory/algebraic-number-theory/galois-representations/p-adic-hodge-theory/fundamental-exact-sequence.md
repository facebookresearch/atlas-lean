# Fundamental exact sequence of p-adic Hodge theory

Let $K$ be a finite extension of $\mathbb{Q}_p$ and $B_e = B_{\mathrm{cris}}^{\varphi = 1}$. Then
$B_e \cap B_{\mathrm{dR}}^+ = \operatorname{Fil}^0 B_e = \mathbb{Q}_p$, and the sequences of $G_K$-modules

$$0 \to \mathbb{Q}_p \xrightarrow{x \mapsto (x, x)} B_e \oplus B_{\mathrm{dR}}^+ \xrightarrow{(y, z) \mapsto y - z} B_{\mathrm{dR}} \to 0,
\qquad 0 \to \mathbb{Q}_p \to B_e \to B_{\mathrm{dR}}/B_{\mathrm{dR}}^+ \to 0$$

are exact. Moreover the sequence

$$0 \to \mathbb{Q}_p \xrightarrow{\ \alpha\ } B_{\mathrm{cris}} \oplus B_{\mathrm{dR}}^+ \xrightarrow{\ \beta\ } B_{\mathrm{cris}} \oplus B_{\mathrm{dR}} \to 0,
\qquad \alpha(x) = (x, x), \quad \beta(y, z) = (y - \varphi(y), \, y - z),$$

is exact; in particular $1 - \varphi$ is surjective on $B_{\mathrm{cris}}$, and $\varphi$ is injective on it.

## Depends on

- [Crystalline representations](crystalline-representations.md), for $B_{\mathrm{cris}}$, its Frobenius and its embedding in $B_{\mathrm{dR}}$
- [de Rham representations](de-rham-representations.md), for $B_{\mathrm{dR}}^+$ and $B_{\mathrm{dR}}$

## Proof depends on

- [Structure of the rings of periods](structure-of-the-period-rings.md), for the description of $(B_{\mathrm{cris}}^+)^{\varphi = p^d}$ through the logarithm of $1 + \mathfrak{m}_R$ and the fundamental lemma (its items 2 and 3)

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §7.3, Definition 7.27 ($B_e$), Theorem 7.28 (1) ($\operatorname{Fil}^0 B_e = \mathbb{Q}_p$) and (4) (the exact sequence
  (7.27)) with its proof, and Remark 7.29 (the fundamental exact sequence, also in the form (7.28)); the remark
  after Theorem 8.4 ($\varphi$ is injective on $B_{\mathrm{st}} \supseteq B_{\mathrm{cris}}$).
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: the proof of
  Proposition 2.8 (the exact sequence with $\alpha$ and $\beta$, cited from Colmez) and Exercise 2.20.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  bundles these properties of $B_{\mathrm{cris}}$ (injectivity of $\varphi$ and of $K \otimes B_{\mathrm{cris}} \to B_{\mathrm{dR}}$,
  the fundamental sequence, and the solvability of $\varphi(x) - x = y$ with $x \in \operatorname{Fil}^0$) as
  `GlobalTheory.Published.FontaineBcris`.
