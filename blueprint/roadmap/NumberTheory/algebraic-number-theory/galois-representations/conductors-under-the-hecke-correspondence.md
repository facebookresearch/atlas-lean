# Conductors under Carayol's Hecke correspondence

Let $F$ be a finite extension of $\mathbb{Q}_p$ whose residue field has $q$ elements, $\pi$ an irreducible admissible
infinite-dimensional representation of $\mathrm{GL}_2(F)$, and $\sigma(\pi)$ the Frobenius-semisimple Weil–Deligne
representation attached to it by [Carayol's Hecke correspondence](carayol-s-hecke-correspondence.md). For a nontrivial
additive character $\psi$ of $F$ let $c(\psi)$ be the largest integer $r$ such that $\psi$ is trivial on
$\mathfrak{p}_F^{-r}$. The $\varepsilon$-factor of $\pi$ has the form

$$\varepsilon(\pi, \psi, s) = \varepsilon(\pi, \psi, 0)\, q^{-s(f(\pi) + 2c(\psi))}$$

for an integer $f(\pi) \ge 0$, the **exponent** of $\pi$, which does not depend on $\psi$. Then the
[conductor](conductor-of-a-weil-deligne-representation.md) of $\sigma(\pi)$ is the exponent of $\pi$:

$$a(\sigma(\pi)) = f(\pi).$$

## Expansion

This node is still to be broken down. A good expansion states and links:

1. the exponent of the $\varepsilon$-factor of a Frobenius-semisimple Weil–Deligne representation
   $\sigma = (V, r, N)$ of $W_F$: $\varepsilon(\sigma, \psi, s) = \varepsilon(\sigma, \psi, 0)\, q^{-s(a(\sigma) + \dim(V) c(\psi))}$. For the
   semisimple representation $r$ of $W_F$ this is Bushnell–Henniart–Kutzko's statement that the exponent is the
   Artin conductor of $r$ plus $\dim(V)\, c(\psi)$ (§1.3, p. 538, citing Tate's Corvallis article, §3; not read here);
   the factor $\det(-q^{-s} r(\Phi) \mid V^{I_F}/V_N^{I_F})$ by which the
   [factors of Weil–Deligne representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md)
   differ from those of $r$ adds $\dim V^{I_F} - \dim V_N^{I_F}$, giving $a(\sigma)$;
2. the form of $\varepsilon(\pi, \psi, s)$ above, with $f(\pi)$ an integer, nonnegative and independent of $\psi$
   (Bushnell–Henniart–Kutzko, §1.3, p. 538; Wedhorn, (2.5.4));
3. the behaviour of both kinds of $\varepsilon$-factors under twists by the unramified characters $\omega^{s_0}$,
   $\omega = \lvert \cdot \rvert_F$, which shift $s$ by $s_0$ and so leave the exponents unchanged: $f(\omega^{1/2}.\pi) = f(\pi)$;
4. the invariance of the conductor of a Weil–Deligne representation under the contragredient,
   $a(\check\sigma) = a(\sigma)$: $(V^\vee)^{I_F}$ is the dual of $V^{I_F}$ for the finite group $r(I_F)$, the same holds for
   the groups $G_F^u$, and $N$ commutes with $r(I_F)$, so that the kernel of the transpose of $N$ on the dual of $V^{I_F}$
   has the dimension of $V_N^{I_F}$;
5. the conclusion: Carayol's identity $\varepsilon(\check\sigma(\pi), \psi, s) = \varepsilon(\omega^{1/2}.\pi, \psi, s)$ (the case $\chi = 1$)
   and items 1–3 give $a(\check\sigma(\pi)) = f(\omega^{1/2}.\pi) = f(\pi)$, and item 4 gives $a(\sigma(\pi)) = f(\pi)$. For
   supercuspidal representations and $\mathrm{rec}_n$, Wedhorn (4.2.5) draws the same conclusion from the preservation of
   $\varepsilon$-factors.

## Depends on

- [Carayol's Hecke correspondence for GL₂](carayol-s-hecke-correspondence.md), for $\sigma(\pi)$
- [Conductor of a Weil–Deligne representation](conductor-of-a-weil-deligne-representation.md), for $a(\sigma(\pi))$
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md), for $\varepsilon(\pi, \psi, s)$ and its exponent

## Proof depends on

- [Carayol's Hecke correspondence for GL₂](carayol-s-hecke-correspondence.md), for $\varepsilon(\chi.\check\sigma(\pi), \psi, s) = \varepsilon(\chi.\omega^{1/2}.\pi, \psi, s)$
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md), for the $\varepsilon$-factors of Weil–Deligne representations through those of representations of $W_F$
- [Weil–Deligne representations](weil-deligne-representations/weil-deligne-representations.md), for the contragredient and for $N$ commuting with $r(I_F)$

## Sources

- C. J. Bushnell, G. Henniart and P. C. Kutzko, "Correspondance de Langlands locale pour $\mathrm{GL}_n$ et
  conducteurs de paires", Ann. Sci. École Norm. Sup. (4) 31 (1998), no. 4, 537–560,
  doi:10.1016/S0012-9593(98)80106-7, §1.3, p. 538: for a semisimple representation $\sigma$ of $\mathcal{W}_F$ of
  dimension $n$, "$\varepsilon(\sigma, \psi_F, s) = \varepsilon(\sigma, \psi_F, 0)\, q_F^{-s(f(\sigma) + nc(\psi_F))}$. Dans cette
  formule, $f(\sigma)$ est l'exposant du conducteur d'Artin de $\sigma$ et $c(\psi_F)$ est le plus grand entier $r$ tel
  que $\psi_F$ soit trivial sur $\mathfrak{p}_F^{-r}$", and for $\pi$ of $\mathrm{GL}_n(F)$ the same form with
  "$f(\pi)$ est un entier (positif d'après [19]) appelé *l'exposant de* $\pi$".
- H. Carayol, "Sur les représentations $l$-adiques associées aux formes modulaires de Hilbert", Ann. Sci. École
  Norm. Sup. (4) 19 (1986), no. 3, 409–468, doi:10.24033/asens.1512, §0.5, p. 410 (the identities characterizing
  $\sigma(\pi_\mathfrak{p})$).
- W. Casselman, "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301–314, Remark, pp. 306–307: the
  factor $\varepsilon(s, \varrho, \psi)$ of Jacquet–Langlands "will have the form $\varepsilon(\varrho, \psi) \cdot
  N\mathfrak{p}^{(2c(\psi) - \delta)s}$ where $\varepsilon(\varrho, \psi)$ is independent of $s$ and $c(\psi)$ is the exponent of the
  conductor of $\psi$".
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.5.4) ($f(\pi)$ and $\varepsilon(\pi, \psi, s) = \varepsilon(\pi, \psi, 0)\, q^{-s(f(\pi) + n\,n(\psi))}$),
  (3.2.1)–(3.2.2) (the $\varepsilon$-factor of a Weil–Deligne representation and the conductor of an irreducible one,
  "by the equality $\varepsilon(\rho, \psi, s) = \varepsilon(\rho, \psi, 0) q^{-s(f(\rho) + n n(\psi))}$"), and (4.2.5) ("Because of
  the preservation of ε-factors in pairs it follows from (3.2.2) and (2.5.4) that $\mathrm{rec}_n$ preserves conductors").
