# Carayol's Hecke correspondence for GL₂

Let $F$ be a finite extension of $\mathbb{Q}_p$ with Weil group $W_F$, and identify characters of $F^\times$ with
characters of $W_F$ through the isomorphism $\mathrm{Art}_F$ of
[Weil group of a p-adic field](weil-deligne-representations/weil-group-of-a-p-adic-field.md), which sends
uniformizers to geometric Frobenius elements. Write $\omega = \lvert \cdot \rvert_F$ and $\omega^s$ for its complex
powers, and, for a character $\chi$ of $F^\times$, $\chi.\pi = \pi \otimes (\chi \circ \det)$ for a representation
$\pi$ of $\mathrm{GL}_2(F)$ and $\chi.\sigma = \sigma \otimes \chi$ for a Weil–Deligne representation $\sigma$ of
$W_F$; $\check\sigma$ is the contragredient and $\chi_\pi$ the central character of $\pi$.

For an irreducible admissible infinite-dimensional representation $\pi$ of $\mathrm{GL}_2(F)$, Carayol's
**Hecke correspondence** attaches the Frobenius-semisimple two-dimensional complex
[Weil–Deligne representation](weil-deligne-representations/weil-deligne-representations.md) $\sigma(\pi)$ of
$W_F$ characterized by

$$L(\chi.\check\sigma(\pi), s) = L(\chi.\omega^{1/2}.\pi, s), \qquad
\varepsilon(\chi.\check\sigma(\pi), s, \psi) = \varepsilon(\chi.\omega^{1/2}.\pi, s, \psi)$$

for every character $\chi$ of $F^\times$ and every nontrivial additive character $\psi$ of $F$, with the factors of
[L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md).
It differs from the [local Langlands correspondence](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/local-langlands-correspondence-for-gl-n.md)
by the twist by $\omega^{1/2}$ followed by the contragredient:

$$\sigma(\pi) \cong \bigl(\mathrm{rec}_2(\pi) \otimes \omega^{1/2}\bigr)^{\vee}.$$

It satisfies:

1. for an irreducible principal series $\pi = \mathrm{Ind}(\xi_1, \xi_2)$,
   $\sigma(\pi) = \xi_1^{-1}\omega^{-1/2} \oplus \xi_2^{-1}\omega^{-1/2}$, with $N = 0$; here $\mathrm{Ind}(\xi_1, \xi_2)$, Carayol's
   unitary induction, is the [normalized parabolic induction](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md)
   from the upper triangular Borel subgroup of the character
   $\left(\begin{smallmatrix} a & 0 \\ 0 & b \end{smallmatrix}\right) \mapsto \xi_1(a)\xi_2(b)$ of the diagonal torus;
2. $\det \sigma(\pi) = \chi_\pi^{-1} \omega^{-1}$;
3. $\sigma(\chi.\pi) = \chi^{-1}.\sigma(\pi)$ for every character $\chi$ of $F^\times$.

**λ-adic realizations.** Let $E \subset \mathbb{C}$ be a number field over which $\sigma(\pi) = (V, r, N)$ has a
model, a Weil–Deligne representation $(V_E, r_E, N_E)$ over $E$ with $(V_E, r_E, N_E) \otimes_E \mathbb{C} \cong
\sigma(\pi)$. For a finite place $\lambda$ of $E$ whose residue characteristic $\ell$ differs from $p$, a lift
$\Phi \in W_F$ of the geometric Frobenius and a nonzero continuous homomorphism $t_\ell \colon I_F \to \mathbb{Q}_\ell$,
the $\lambda$-adic realization $\sigma^\lambda(\pi)$ is the continuous representation of $W_F$ on
$V_E \otimes_E E_\lambda$ given by

$$\sigma^\lambda(\pi)(\Phi^m \tau) = r_E(\Phi^m \tau) \exp\bigl(t_\ell(\tau) N_E\bigr) \qquad (m \in \mathbb{Z}, \ \tau \in I_F),$$

whose isomorphism class does not depend on $\Phi$ and $t_\ell$.

## Expansion

This node is still to be broken down. A good expansion states and links:

1. the existence of $\sigma(\pi)$: the representation $(\mathrm{rec}_2(\pi) \otimes \omega^{1/2})^\vee$ satisfies the
   two identities, by the preservation of the factors of pairs with characters of $F^\times$ and the compatibility
   with twists and contragredients of $\mathrm{rec}_2$, together with $L(\chi \times \pi, s) = L(\chi.\pi, s)$ and
   $\varepsilon(\chi \times \pi, s, \psi) = \varepsilon(\chi.\pi, s, \psi)$ for a character $\chi$ (Bushnell–Henniart–Kutzko,
   §1.3, p. 538); its uniqueness: if $\sigma'$ also satisfies the two identities, the preimage $\Pi'$ of $\check\sigma'$ under
   $\mathrm{rec}_2$ has the $L$- and $\varepsilon$-factors of the twists of $\omega^{1/2}.\pi$, so that $\Pi' \cong \omega^{1/2}.\pi$, hence
   $\sigma' \cong \sigma(\pi)$, by the bijectivity of $\mathrm{rec}_2$ and the
   [local converse theorem for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/local-converse-theorem-for-gl-n.md)
   with $n = 2$, once $\Pi'$ is known to be generic, the converse theorem comparing generic representations. A
   non-generic irreducible $\Pi'$ is a character $\chi \circ \det$; its twist by $\chi^{-1}$, the trivial representation, has
   the $L$-factor $L(\lvert\cdot\rvert^{1/2}, s)\,L(\lvert\cdot\rvert^{-1/2}, s)$ of $\lvert\cdot\rvert^{1/2} \oplus \lvert\cdot\rvert^{-1/2}$, which no twist of
   an infinite-dimensional irreducible representation has (an irreducible $\mathrm{Ind}(\xi_1, \xi_2)$ with this $L$-factor
   would have $\xi_1\xi_2^{-1} = \lvert\cdot\rvert^{\pm 1}$), so that case does not occur;
2. the agreement of the correspondence of Kutzko, through which Carayol defines $\sigma(\pi)$, with
   $\mathrm{rec}_2$, both being normalized by class field theory with geometric Frobenius elements corresponding to
   uniformizers;
3. the value of $\mathrm{rec}_2$ on an irreducible principal series, $\mathrm{rec}_2(\mathrm{Ind}(\xi_1, \xi_2)) = \xi_1
   \oplus \xi_2$ for unitary induction: in the
   [Langlands classification for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md)
   an irreducible $\mathrm{Ind}(\xi_1, \xi_2)$ is $L(\{\xi_1\}, \{\xi_2\})$, for two segments of length one, and the
   [construction of the correspondence](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/construction-of-the-local-langlands-correspondence.md)
   gives $\mathrm{rec}(L(\Delta_1, \dots, \Delta_r)) = \bigoplus_i \mathrm{rec}(\pi_i) \otimes \mathrm{Sp}(m_i)$ for
   $\Delta_i = [\pi_i, \nu^{m_i - 1}\pi_i]$, here with $m_1 = m_2 = 1$; this gives item 1, and the determinant and twist identities 2 and 3, from those of $\mathrm{rec}_2$;
4. the rationality of $\sigma(\pi)$ when $\pi$ is defined over a number field, which Carayol takes from Waldspurger
   and Deligne (§0.5–§0.6, p. 410, citing [W] and [D.1]; not read here), and the realization of a Weil–Deligne
   representation over $E_\lambda$ as a continuous $\lambda$-adic representation of $W_F$ (Ulmer, §8, p. 2296: "given a
   Weil-Deligne representation $(\rho, N)$ on $V$, the displayed formula defines an $\ell$-adic representation. This
   correspondence gives a bijection on isomorphism classes", independent of the choices after Deligne).

## Depends on

- [Local Langlands correspondence for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/local-langlands-correspondence-for-gl-n.md), for $\mathrm{rec}_2$
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md), for the $L$- and $\varepsilon$-factors on both sides
- [Weil–Deligne representations](weil-deligne-representations/weil-deligne-representations.md), for Frobenius-semisimple Weil–Deligne representations, twists, contragredients and determinants
- [Weil group of a p-adic field](weil-deligne-representations/weil-group-of-a-p-adic-field.md), for $W_F$, $I_F$, the geometric Frobenius and $\mathrm{Art}_F$
- [Smooth and admissible representations of p-adic groups](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for irreducible admissible representations of $\mathrm{GL}_2(F)$, their twists and central characters
- [Parabolic induction and Jacquet functors](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for the normalized induction $\mathrm{Ind}(\xi_1, \xi_2)$ from the upper triangular Borel subgroup of $\mathrm{GL}_2(F)$

## Proof depends on

- [Local Langlands correspondence for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/local-langlands-correspondence-for-gl-n.md), for the properties of $\mathrm{rec}_2$: preservation of the factors of pairs, bijectivity, and compatibility with twists, determinants and contragredients
- [Local converse theorem for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/local-converse-theorem-for-gl-n.md), for $n = 2$, which with the bijectivity of $\mathrm{rec}_2$ gives the uniqueness of $\sigma(\pi)$ (expansion item 1)
- [Langlands classification for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/langlands-classification-for-gl-n.md), for an irreducible $\mathrm{Ind}(\xi_1, \xi_2)$ being $L(\{\xi_1\}, \{\xi_2\})$ (expansion item 3)
- [Construction of the local Langlands correspondence for GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/construction-of-the-local-langlands-correspondence.md), for $\mathrm{rec}(L(\Delta_1, \dots, \Delta_r)) = \bigoplus_i \mathrm{rec}(\pi_i) \otimes \mathrm{Sp}(m_i)$, which gives $\mathrm{rec}_2(\mathrm{Ind}(\xi_1, \xi_2)) = \xi_1 \oplus \xi_2$ (expansion item 3)

## Sources

- H. Carayol, "Sur les représentations $l$-adiques associées aux formes modulaires de Hilbert", Ann. Sci. École
  Norm. Sup. (4) 19 (1986), no. 3, 409–468, doi:10.24033/asens.1512:
  - §0.4, pp. 409–410: class field theory normalized "de sorte que les éléments de Frobenius *géométriques*
    correspondent aux uniformisantes", characters of $F_\mathfrak{p}^*$ read as characters of the local Weil group,
    $\omega_\mathfrak{p}^s = \lvert \cdot \rvert_\mathfrak{p}^s$, $\chi.\pi = \pi \otimes (\chi \circ \det)$ and $\chi.\sigma = \sigma \otimes \chi$;
  - §0.5, p. 410, "Correspondance de Hecke": $\sigma(\pi_\mathfrak{p})$, "F-semisimple de degré 2, du groupe de
    Weil-Deligne local" (cf. [Ta]), "caractérisée par les égalités suivantes, pour chaque quasi-caractère $\chi$ de
    $F_\mathfrak{p}^*$: $L(\chi.\check\sigma(\pi_\mathfrak{p})) = L(\chi.\omega_\mathfrak{p}^{1/2}.\pi_\mathfrak{p})$,
    $\varepsilon(\chi.\check\sigma(\pi_\mathfrak{p})) = \varepsilon(\chi.\omega_\mathfrak{p}^{1/2}.\pi_\mathfrak{p})$", resting on
    Kutzko's work [Ku] (not read here); "La correspondance « de Hecke » ainsi définie diffère de la correspondance de
    Langlands par torsion par le caractère $\omega_\mathfrak{p}^{1/2}$ suivie du passage à la contragrédiente"; the
    principal series formula $\sigma(\pi_\mathfrak{p}) = \xi_1^{-1}.\omega_\mathfrak{p}^{-1/2} \oplus \xi_2^{-1}.\omega_\mathfrak{p}^{-1/2}$
    for $\pi_\mathfrak{p} = \mathrm{Ind}(\xi_1, \xi_2)$ (induction unitaire); properties (a)
    $\det \sigma(\pi_\mathfrak{p}) = \chi_{\pi_\mathfrak{p}}^{-1}.\omega_\mathfrak{p}^{-1}$ and (b)
    $\sigma(\chi.\pi_\mathfrak{p}) = \chi^{-1}.\sigma(\pi_\mathfrak{p})$;
  - §0.6, p. 410: the realizations over a finite extension $E$ of the field of rationality $\mathbb{Q}(\pi)$ and, for
    each finite place $\lambda$ of $E$ of residue characteristic different from that of $\mathfrak{p}$, "une
    représentation $\lambda$-adique continue $\sigma^\lambda(\pi_\mathfrak{p})$ du groupe de Weil local".
- C. J. Bushnell, G. Henniart and P. C. Kutzko, "Correspondance de Langlands locale pour $\mathrm{GL}_n$ et
  conducteurs de paires", Ann. Sci. École Norm. Sup. (4) 31 (1998), no. 4, 537–560,
  doi:10.1016/S0012-9593(98)80106-7: §1.1 (reciprocity normalized with geometric Frobenius elements corresponding
  to uniformizers) and §1.3, p. 538 (for a character $\chi$, $L(\chi \times \pi_2) = L(\chi\pi_2)$ and
  $\varepsilon(\chi \times \pi_2, \psi_F) = \varepsilon(\chi\pi_2, \psi_F)$).
- D. Ulmer, "Conductors of ℓ-adic representations", Proc. Amer. Math. Soc. 144 (2016), no. 6, 2291–2299,
  doi:10.1090/proc/12880: §8, p. 2296 (the formula (8.1) and the bijection between Weil–Deligne representations
  and $\ell$-adic representations of $W_F$, after Deligne).
