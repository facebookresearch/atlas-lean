# Fundamental exact sequence of p-adic Hodge theory

Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete discretely valued field of characteristic $0$ whose residue field is perfect of characteristic $p$ (for instance a finite extension of $\mathbb{Q}_p$) and $B_e = B_{\mathrm{cris}}^{\varphi = 1}$. Then
$B_e \cap B_{\mathrm{dR}}^+ = \operatorname{Fil}^0 B_e = \mathbb{Q}_p$, and the sequences of $G_K$-modules

$$0 \to \mathbb{Q}_p \xrightarrow{x \mapsto (x, x)} B_e \oplus B_{\mathrm{dR}}^+ \xrightarrow{(y, z) \mapsto y - z} B_{\mathrm{dR}} \to 0,
\qquad 0 \to \mathbb{Q}_p \to B_e \to B_{\mathrm{dR}}/B_{\mathrm{dR}}^+ \to 0$$

are exact. Moreover the sequence

$$0 \to \mathbb{Q}_p \xrightarrow{\ \alpha\ } B_{\mathrm{cris}} \oplus B_{\mathrm{dR}}^+ \xrightarrow{\ \beta\ } B_{\mathrm{cris}} \oplus B_{\mathrm{dR}} \to 0,
\qquad \alpha(x) = (x, x), \quad \beta(y, z) = (y - \varphi(y), \, y - z),$$

is exact; in particular $1 - \varphi$ is surjective on $B_{\mathrm{cris}}$, and $\varphi$ is injective on it. More
precisely, with $\operatorname{Fil}^0 B_{\mathrm{cris}} = B_{\mathrm{cris}} \cap B_{\mathrm{dR}}^+$, the sequence

$$0 \to \mathbb{Q}_p \to \operatorname{Fil}^0 B_{\mathrm{cris}} \xrightarrow{\ \varphi - 1\ } B_{\mathrm{cris}} \to 0$$

is exact: every $y \in B_{\mathrm{cris}}$ is $\varphi(x) - x$ for some $x \in B_{\mathrm{cris}}$ with $x \in B_{\mathrm{dR}}^+$.

## Depends on

- [Crystalline representations](crystalline-representations.md), for $B_{\mathrm{cris}}$, its Frobenius and its embedding in $B_{\mathrm{dR}}$
- [de Rham representations](de-rham-representations.md), for $B_{\mathrm{dR}}^+$ and $B_{\mathrm{dR}}$

## Proof depends on

- [Structure of the rings of periods](structure-of-the-period-rings.md), for Theorem 7.26 (3), the exact sequences $0 \to \mathbb{Q}_p(r) \to \operatorname{Fil}^r B_{\mathrm{cris}} \to B_{\mathrm{cris}} \to 0$ given by $p^{-r}\varphi - 1$, and Theorem 7.28 (1)–(3), from which Theorem 7.28 (4) follows (its items 3 and 4)

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §7.2.3, Theorem 7.26 (3) (for $r \in \mathbb{Z}$, $0 \to \mathbb{Q}_p(r) \to \operatorname{Fil}^r B_{\mathrm{cris}} \xrightarrow{p^{-r}\varphi - 1} B_{\mathrm{cris}} \to 0$ is
  exact; the case $r = 0$); §7.3, Definition 7.27 ($B_e$), Theorem 7.28 (1) ($\operatorname{Fil}^0 B_e = \mathbb{Q}_p$) and (4) (the
  exact sequence (7.27)) with its proof, and Remark 7.29 (the fundamental exact sequence, also in the form (7.28));
  the remark after Theorem 8.4 ($\varphi$ is injective on $B_{\mathrm{st}} \supseteq B_{\mathrm{cris}}$).
- S. Bloch and K. Kato, "L-functions and Tamagawa numbers of motives", in *The Grothendieck Festschrift*, vol. I,
  Progr. Math. 86, Birkhäuser, 1990, 333–400, <http://math.stanford.edu/~conrad/BSDseminar/refs/BKTamagawa.pdf>:
  Proposition 1.17 (the exact sequences (1.17.1) $0 \to \mathbb{Q}_p \to B_{\mathrm{cris}}^{f=1} \oplus B_{\mathrm{dR}}^+ \to B_{\mathrm{dR}} \to 0$ and
  (1.17.2) with $\alpha$ and $\beta$) and its proof ("$1 - f \colon B_{\mathrm{cris}} \to B_{\mathrm{cris}}$ is surjective"), p. 340.
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: the proof of
  Proposition 2.8 (the exact sequence with $\alpha$ and $\beta$, cited from Colmez) and Exercise 2.20.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  bundles seven properties of $B_{\mathrm{cris}}$ as `GlobalTheory.Published.FontaineBcris`. This page supplies four of
  them: the injectivity of $\varphi$ (`PhiInj`), $B_e \cap B_{\mathrm{dR}}^+ = \mathbb{Q}_p$ (`Fund`),
  $B_e + B_{\mathrm{dR}}^+ = B_{\mathrm{dR}}$ (`FundOnto`) and the surjectivity of $\varphi - 1$ from
  $\operatorname{Fil}^0 B_{\mathrm{cris}}$ onto $B_{\mathrm{cris}}$ (`PhiSubOneOntoFilZero`). The other three, the injectivity of
  $B_{\mathrm{cris}} \to B_{\mathrm{dR}}$ and of $K \otimes_{K_0} B_{\mathrm{cris}} \to B_{\mathrm{dR}}$ and the regularity of $B_{\mathrm{cris}}$
  (`IotaInj`, `TensorInj`, `Regular`), are on the page on [crystalline representations](crystalline-representations.md).
