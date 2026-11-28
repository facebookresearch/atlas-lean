# Bloch–Kato subgroups of local Galois cohomology

Let $K$ be a finite extension of $\mathbb{Q}_p$ and $V$ a $p$-adic representation of $G_K$. In continuous
cohomology, the **Bloch–Kato subgroups** of $H^1(G_K, V)$ are

$$H^1_e(G_K, V) = \ker\bigl(H^1(G_K, V) \to H^1(G_K, B_{\mathrm{cris}}^{\varphi = 1} \otimes_{\mathbb{Q}_p} V)\bigr),$$
$$H^1_f(G_K, V) = \ker\bigl(H^1(G_K, V) \to H^1(G_K, B_{\mathrm{cris}} \otimes_{\mathbb{Q}_p} V)\bigr),$$
$$H^1_g(G_K, V) = \ker\bigl(H^1(G_K, V) \to H^1(G_K, B_{\mathrm{dR}} \otimes_{\mathbb{Q}_p} V)\bigr),$$

so that $H^1_e \subseteq H^1_f \subseteq H^1_g$, since $B_{\mathrm{cris}}^{\varphi = 1} \subseteq B_{\mathrm{cris}} \subseteq B_{\mathrm{dR}}$.
Interpreting a class as an extension $0 \to V \to W \to \mathbb{Q}_p \to 0$, it lies in $H^1_f$ if and only if
$0 \to D_{\mathrm{cris}}(V) \to D_{\mathrm{cris}}(W) \to D_{\mathrm{cris}}(\mathbb{Q}_p) \to 0$ is exact, and in $H^1_g$ if
and only if the analogous sequence for $D_{\mathrm{dR}}$ is exact; in particular, for crystalline $V$ the class lies
in $H^1_f$ if and only if $W$ is crystalline, and for de Rham $V$ it lies in $H^1_g$ if and only if $W$ is de
Rham. For an $\ell$-adic representation of $G_K$ with $\ell \ne p$, the analogous subgroup is the unramified one,
$\ker(H^1(G_K, V) \to H^1(I_K, V))$.

## Depends on

- [Crystalline representations](crystalline-representations.md), for $B_{\mathrm{cris}}$ and $D_{\mathrm{cris}}$
- [de Rham representations](de-rham-representations.md), for $B_{\mathrm{dR}}$ and $D_{\mathrm{dR}}$
- [Galois cohomology of ℓ-adic representations of a p-adic field](../galois-cohomology-of-local-fields/galois-cohomology-of-l-adic-representations.md), for continuous cohomology with $p$-adic coefficients

## Proof depends on

- [Admissible representations for a regular ring of periods](admissible-representations.md), for the dimension criterion, which, for crystalline (or de Rham) $V$, makes the exactness of the sequence of $D_{\mathrm{cris}}$ (or $D_{\mathrm{dR}}$) equivalent to $W$ being crystalline (or de Rham)
- [The long exact sequence of continuous cohomology](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/continuous-cochain-cohomology/long-exact-sequence-for-continuous-cohomology.md), for the long exact sequence of continuous cohomology of $0 \to B \otimes V \to B \otimes W \to B \to 0$ for $B = B_{\mathrm{cris}}$ or $B_{\mathrm{dR}}$, which has a continuous section since it splits $B$-linearly; its connecting map sends $1 \in B^{G_K}$ to the image of the class of the extension

## Sources

- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: §2.2.1, Definition 2.5
  ($H^1_f$) and Lemma 2.5 (extensions); §2.2.2, the definitions of $H^1_g$ and $H^1_e$, the inclusions and
  Lemma 2.7; §2.1.4, Definition 2.1 (the unramified $H^1$). The groups are those of S. Bloch and K. Kato,
  "L-functions and Tamagawa numbers of motives", The Grothendieck Festschrift I, Progr. Math. 86, Birkhäuser,
  1990, 333–400.
- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §9.3, Definition 9.22 (Kato's filtration $H^1_e \subseteq H^1_f \subseteq H^1_{\mathrm{st}} \subseteq H^1_g$).
