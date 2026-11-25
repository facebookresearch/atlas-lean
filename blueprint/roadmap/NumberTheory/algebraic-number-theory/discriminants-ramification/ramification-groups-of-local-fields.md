# Ramification groups of local fields

This node is still to be broken down. It covers the lower numbering filtration of the Galois group of a finite
Galois extension of local fields and the structure results on its quotients, which give the structure of the
inertia and wild inertia groups of a $p$-adic field. Let $L/K$ be a finite Galois extension of complete
discretely valued fields whose residue fields are perfect of characteristic $p > 0$, $G = \operatorname{Gal}(L/K)$,
and for $i \ge -1$ let
$G_i = \{ s \in G : v_L(s(x) - x) \ge i + 1 \text{ for all } x \in \mathcal{O}_L \}$.

A good expansion has pages for:

1. the definition of the ramification groups $G_i$, the identification of $G_0$ with the inertia group and of
   $G_{-1}/G_0$ with the Galois group of the residue extension (Fontaine–Ouyang, Lemma 1.58, Proposition 1.59,
   Definition 1.60, Remark 1.61);
2. the description of $G_i$ inside $G_0$ by $s(\pi_L)/\pi_L \in U_L^i$ for a uniformizer $\pi_L$ (Proposition 1.62),
   the structure of the unit filtration (Proposition 1.63), and the injective homomorphisms
   $\theta_i \colon G_i/G_{i+1} \hookrightarrow U_L^i/U_L^{i+1}$, $s \mapsto s(\pi_L)/\pi_L$, independent of $\pi_L$
   (Proposition 1.64, (1.34));
3. the consequences, which use that the residue characteristic $p$ is positive: $G_0/G_1$ is cyclic of order prime
   to $p$ and embeds in $\mu(k_L)$ through $\theta_0$, the quotients $G_i/G_{i+1}$ for $i \ge 1$ are elementary
   abelian $p$-groups, $G_1$ is a normal $p$-subgroup and $G_0 \cong G_1 \rtimes C$ for a cyclic subgroup $C$ of order
   prime to $p$ (Proposition 1.64 (1)–(3), Remark 1.65); with the description of $\theta_0$ through Kummer theory and its
   compatibility (1.35) in towers of Galois extensions;
4. the behaviour of the lower numbering under passage to subgroups, $H_i = G_i \cap H$ (Remark 1.61,
   Proposition 1.67).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Eisenstein criterion for total ramification of discrete valuation rings](../../../RingTheory/ramification/totally-ramified-extensions-and-eisenstein-polyn/ramification-idx-eq-finrank-iff-eisenste.md), for $\mathcal{O}_L = \mathcal{O}_{L_0}[\pi_L]$ for the totally ramified extension $L/L_0$, where $L_0$ is the fixed field of $G_0$, through which Proposition 1.62 tests $G_i$ on a uniformizer (item 2)
- [Hensel's lemma for complete discrete valuation rings](../../../RingTheory/valuation-rings/henselian-rings-and-hensel-s-lemma/exists-is-root-sub-mem-maximal-ideal-of.md), for the primitive $N$-th roots of unity, $N = (G_0 : G_1)$, in $L_0$, in the description of $\theta_0$ on the tame, totally ramified part $L_1/L_0$ of item 3 (Fontaine–Ouyang, Remark 1.65 (b))
- [Kummer theory for abelian extensions of exponent dividing n](../../../FieldTheory/galois-theory/kummer-theory.md), for $L_1 = L_0(\alpha)$ with $\alpha^N$ a uniformizer of $L_0$, where $L_1$ is the fixed field of $G_1$, in that description

## Expansion

A good expansion also states and links:

- the Teichmüller representatives of the residue field (Fontaine–Ouyang, Remark 1.65 (b)), for the formula $g \alpha = [\varepsilon] \alpha$ through which $\theta_0$ identifies $\operatorname{Gal}(L_1/L_0)$ with $\mu_N(k_L)$ in the description of $\theta_0$ of item 3
- the existence of a complement to a normal subgroup whose order is prime to its index, the existence part of the Schur–Zassenhaus theorem as opposed to the conjugacy of complements, here to the $p$-group $G_1$ in $G_0$ (Fontaine–Ouyang, Proposition 1.64 (3)), for the semidirect product decomposition of item 3

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §1.1, Definition 1.16 (local fields have perfect residue fields of characteristic $p > 0$); §1.3.1, Lemma 1.58
  to Remark 1.65, diagram (1.35), and Proposition 1.67.
- J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979: Chapter IV, §§1–2, the source
  followed by Fontaine–Ouyang.
