# Structure of the rings of periods

This node is still to be broken down. It covers the constructions and structure theorems for Fontaine's rings
of periods that the proofs of the pages on $p$-adic Hodge theory use, following Fontaine–Ouyang, Chapters 1 and
4–9. Let $K$ be a $p$-adic field in the sense of Fontaine–Ouyang, a complete discretely valued field of characteristic $0$ whose residue field is perfect of characteristic $p$ (for instance a finite extension of $\mathbb{Q}_p$) and $C$ the completion of $\bar K$.

A good expansion has pages for:

1. Tate's normalized traces on the cyclotomic $\mathbb{Z}_p$-extension and Sen's theory of $C$-representations
   (Fontaine–Ouyang, §1.4, Definition 1.100, Propositions 1.102–1.104; Chapter 4, Theorems 4.33, 4.40 and
   Proposition 4.43), with the continuous cohomology of $C$-representations that the proofs of the
   [Tate–Sen theorem](tate-sen-theorem.md) use, that theorem itself not being part of this node: the Tate–Sen
   formalism for the tower $K_\infty/K$ cut out by an infinitely ramified continuous character $\psi$ of $G_K$, that is,
   one with $\psi(I_K)$ infinite, whose image contains $\mathbb{Z}_p$ as an open subgroup, of which the cyclotomic tower
   is one example (Brinon–Conrad, §14.1, Sen's situation, and Lemma 14.1.3); after replacing $K$ by a finite layer of
   the tower over which $\Gamma = \mathrm{Gal}(K_\infty/K) \simeq \mathbb{Z}_p$ and choosing a topological generator $\gamma$ of
   $\Gamma$, the bijectivity of $\gamma - \lambda$ on $\hat K_\infty$ for a $1$-unit $\lambda$ that is not a $p$-power root of
   unity (Lemma 14.1.9, for an infinitely ramified $\mathbb{Z}_p$-extension); for $H = G_{K_\infty}$ and a $C$-representation $W$ of $G_K$, the vanishing of
   $H^n_{\mathrm{cont}}(H, W)$ for $n \ge 1$ and the inflation isomorphisms
   $H^n_{\mathrm{cont}}(G_K/H, W^H) \cong H^n_{\mathrm{cont}}(G_K, W)$ for $n \ge 0$ (Propositions 14.3.2 and 14.3.3), proved by
   hand in degrees $n \ge 2$, as there is no Hochschild–Serre spectral sequence for continuous cochains with such
   coefficients (the preliminary version leaves the injectivity argument in those degrees unfinished, n. 8); the
   inflation–restriction sequence in degree $1$ for continuous $1$-cocycles with such coefficients, and, for a finite
   Galois extension $K'/K$ and a $C$-representation $W$ of $G_K$, the restriction isomorphism
   $H^1_{\mathrm{cont}}(G_K, W) \cong H^1_{\mathrm{cont}}(G_{K'}, W)^{\mathrm{Gal}(K'/K)}$ onto the $\mathrm{Gal}(K'/K)$-invariants of the
   cohomology of the subgroup, the cohomology of the finite group $\mathrm{Gal}(K'/K)$ vanishing in positive degrees on
   $\mathbb{Q}$-vector spaces (proof of Theorem 14.3.4); the continuous cohomology of the procyclic group
   $\Gamma_{K_m} = \mathrm{Gal}(K_\infty/K_m)$ on $\hat K_\infty(i)$, in degree $1$ through, for $m$ sufficiently large, the
   decomposition $\hat K_\infty = K_m \oplus X_m$ by normalized traces and the invertibility of
   $\chi(\gamma_m)^i \gamma_m - 1$ on $X_m$, passed to $\Gamma_K$ through the finite group $\mathrm{Gal}(K_m/K)$, and its vanishing
   in degrees $n \ge 2$ (Fontaine–Ouyang, proof of Proposition 4.46, with Proposition 1.104);
   and completed unramified descent for finitely generated modules over the completion of the maximal unramified
   extension with a continuous semilinear action of the absolute Galois group of the residue field (Brinon–Conrad,
   Lemma 3.2.6), which identifies $C(\eta)$ with $C$ as $C$-representations of $G_{K'}$ for a continuous character $\eta$
   of $G_K$ and a finite Galois extension $K'/K$ over which $\eta$ is unramified, with ordinary Galois descent along
   $K'/K$ for $K'$-vector spaces with a $K'$-semilinear action of $\mathrm{Gal}(K'/K)$;
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
- [Continuous cohomology](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/continuous-cochain-cohomology/continuous-cohomology.md), for continuous cochain cohomology of topological modules, whose forms for $C$-representations item 1 states

## Proof depends on

- [Ramification groups of local fields](../../discriminants-ramification/ramification-groups-of-local-fields.md), for the lower numbering, on which the ramification estimates behind item 1 are built (Fontaine–Ouyang, §§1.3–1.4)

## Expansion

A good expansion also states and links:

- the ring $W(R)$ of Witt vectors of the perfect ring $R$, with the Teichmüller expansion $\sum_{n \ge 0} p^n [x_n]$ of its elements (Fontaine–Ouyang, §1.2.2), for $\theta \colon W(R) \to \mathcal{O}_C$ and $A_{\mathrm{cris}}$ in item 2
- the local different of an extension of local fields expressed through the upper numbering ((1.54)–(1.55)), the trace estimate of Corollary 1.79, and the ramification of totally ramified $\mathbb{Z}_p$-extensions ((1.68), Sen's filtration theorem), which give the almost étale condition and the estimates of Proposition 1.95 to Corollary 1.99 behind Tate's normalized traces (item 1; Fontaine–Ouyang, §§1.3.3–1.4.2)
- Lubin–Tate formal groups (Fontaine–Ouyang, §7.3.2), for the Lubin–Tate elements of item 4
- Fontaine's equivalence between the $p$-adic representations of the absolute Galois group of a field $E$ of characteristic $p$ and the étale $\varphi$-modules over the characteristic-zero field $\operatorname{Frac} C(E)$, for a Cohen ring $C(E)$ of $E$ (Fontaine–Ouyang, Proposition 3.32, Theorem 3.35), used in the proofs of item 6

## Sources

- J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of 2022-05-26),
  archived at <http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>:
  §1.4, Chapters 4–9, at the locators above.
- O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (preliminary version, 2009),
  <https://math.stanford.edu/~conrad/papers/notes.pdf>: §14.1 (the Tate–Sen conditions, in Sen's situation for an
  infinitely ramified character whose image contains $\mathbb{Z}_p$ as an open subgroup, Lemma 14.1.3, and Lemma
  14.1.9 for an infinitely ramified $\mathbb{Z}_p$-extension with a topological generator of its Galois group), §14.3 (Propositions 14.3.2 and
  14.3.3, "There is no Hochschild-Serre spectral sequence, due to the continuity conditions, but we can adapt the
  idea by working 'by hand'", and the proof of Theorem 14.3.4), Lemma 3.2.6 (completed unramified descent).
