# Structure of the rings of periods

This node is still to be broken down. It covers the constructions and structure theorems for Fontaine's rings
of periods that the proofs of the pages on $p$-adic Hodge theory use, following Fontaine–Ouyang, Chapters 1 and
4–9. Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete discretely valued field of characteristic $0$ whose residue field is perfect of characteristic $p$ (for instance a finite extension of $\mathbb{Q}_p$) and $C$ the completion of $\bar K$.

A good expansion has pages for:

1. Tate's normalized traces on the cyclotomic $\mathbb{Z}_p$-extension and Sen's theory of $C$-representations
   (Fontaine–Ouyang, §1.4, Definition 1.100, Propositions 1.102–1.104; Chapter 4, Theorems 4.33, 4.40 and
   Proposition 4.43);
2. the ring $R$ and its properties, the map $\theta$, the element $t$ and the ring $A_{\mathrm{cris}}$ (Chapter 5,
   Definition 5.4, Theorem 5.5; §6.2, Propositions 6.11, 6.19, 6.22; §7.1.1–7.1.3, Definitions 7.1, 7.3, Propositions
   7.4–7.8), and Fontaine's logarithm (§7.1.4): the series (7.12) on $U_R^1 = \{x \in R : v(x - 1) \ge 1\}$, which does
   not apply to all units of $R$, its extension (7.13) to $U_R^+ = 1 + \mathfrak{m}_R$ by division by powers of $p$, its
   extension (7.14) to $R^\times = \bar k^\times \times U_R^+$ by ignoring the factor in $\bar k^\times$, its extension to
   $(\operatorname{Frac} R)^\times$ through $u = \log[\varpi]$ (7.15), Definition 7.11, Lemma 7.12 and Proposition 7.14
   ($u$ is transcendental);
3. the exact sequences $0 \to \mathbb{Q}_p(r) \to \operatorname{Fil}^r B_{\mathrm{cris}} \xrightarrow{p^{-r}\varphi - 1} B_{\mathrm{cris}} \to 0$
   for $r \in \mathbb{Z}$, and their analogues for $B_{\mathrm{cris}}^+$ with $r \ge 0$ (§7.2.3, Theorem 7.26 (2)–(3));
4. the Frobenius eigenspaces $P^+_{h,d} = (B_{\mathrm{cris}}^+)^{\varphi^h = p^d}$, which are $\mathbb{Q}_p$-vector spaces and
   not rings in general ($t \in P^+_{1,1}$, while $t^2 \in P^+_{1,2}$), with $B_e = B_{\mathrm{cris}}^{\varphi = 1}$
   (Definition 7.27, Theorem 7.28 (1)–(3)), Colmez's fundamental lemma and Lubin–Tate elements (§7.4, Theorem 7.41,
   Propositions 7.42–7.46), and the ring $B_e$ as an almost Euclidean, hence principal ideal, domain
   (Definition 7.50, Proposition 7.51, Theorem 7.53);
5. the Dieudonné–Manin classification of $\varphi$-modules over $K_0$ and the slope filtration of a $\varphi$-module by
   its Newton slopes, which Fontaine–Ouyang call its Harder–Narasimhan filtration (Theorem 8.25, Corollary 8.26,
   Proposition 8.27, Lemmas 8.28–8.29, Corollary 8.30, Propositions 8.31–8.33); these concern the underlying
   $\varphi$-module, not the filtered $(\varphi, N)$-module;
6. the proofs of Fontaine's and Colmez–Fontaine's theorems (Chapter 9: §9.1, §9.2 with the reduction of Theorem B,
   §9.3, and §§9.4–9.5, the reduction to $t_H = 0$ and the end of the proof).

## Depends on

- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for the twists $\mathbb{Q}_p(r)$ of item 3
- [Weakly admissible filtered (φ, N)-modules](weakly-admissible-filtered-phi-n-modules.md), for $\varphi$-modules over $K_0$ and their Newton numbers in item 5
- Not yet a page: Witt vectors and Teichmüller representatives, for $\theta \colon W(R) \to \mathcal{O}_C$ and $A_{\mathrm{cris}}$ in item 2

## Proof depends on

- [Ramification groups of local fields](../../discriminants-ramification/ramification-groups-of-local-fields.md), for the lower numbering, on which the ramification estimates behind item 1 are built (Fontaine–Ouyang, §§1.3–1.4)
- Not yet a page: the functions $\Phi$ and $\Psi$, Herbrand's theorem and the upper numbering, also for infinite Galois extensions, and the different (Fontaine–Ouyang, §§1.3.3–1.3.5), and Sen's filtration theorem (§1.4.1), for the ramification estimates in totally ramified $\mathbb{Z}_p$-extensions behind Tate's normalized traces (item 1)
- Not yet a page: Lubin–Tate formal groups (Fontaine–Ouyang, §7.3.2), for the Lubin–Tate elements of item 4
- Not yet a page: étale $\varphi$-modules in characteristic $p$ and Fontaine's equivalence for them (Fontaine–Ouyang, Proposition 3.32, Theorem 3.35), used in the proofs of item 6

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §1.4, Chapters 4–9, at the locators above.
