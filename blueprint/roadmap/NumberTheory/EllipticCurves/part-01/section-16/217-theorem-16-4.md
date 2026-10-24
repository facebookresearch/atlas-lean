---
article_id: af_57defb53af7f1d8888b916af
declaration: theorem
origin: cited
lean: ComplexLattice.theorem_16_4
---

# Theorem 16.4

For $i=1,2$ let $L_i \subseteq \mathbb{C}$ be a lattice, let $E_i \coloneqq
 E_{L_i}$ be the corresponding elliptic curve, define $\wp_i(z) \coloneqq
 \wp(z; L_i)$, and let $\Phi_i: \mathbb{C}/L_i \rightarrow E_i(\mathbb{C})$
 be the isomorphism that sends $z \notin L_i$ to $(\wp_i(z), \wp_i'(z))$ and
 $z \in L_i$ to 0. For any $\alpha \in \mathbb{C}$, the following are
 equivalent: (1) $\alpha L_1 \subseteq L_2$; (2) $\wp_2(\alpha z) =
 u(\wp_1(z))/v(\wp_1(z))$ for some polynomials $u, v \in \mathbb{C}[x]$; (3)
 There is a unique $\phi_\alpha \in \operatorname{Hom}(E_1, E_2)$ such that
 the diagram $\Phi_2 \circ \alpha = \phi_\alpha \circ \Phi_1$ commutes. For
 every morphism $\phi \in \operatorname{Hom}(E_1, E_2)$ there is a unique
 $\alpha = \alpha_\phi$ satisfying (1)-(3). The maps $\phi \mapsto
 \alpha_\phi$ and $\alpha \mapsto \phi_\alpha$ define inverse isomorphisms of
 $\operatorname{Hom}(E_1, E_2)$ and $\{\alpha \in \mathbb{C} \mid \alpha L_1
 \subseteq L_2\}$.

## Depends on

- [Definition 14.1](../section-14/section-14-1/174-definition-14-1.md)
- [Definition 14.23](../section-14/section-14-4/192-definition-14-23.md)
- [Theorem 15.1](../section-15/202-theorem-15-1.md)

## Proof depends on

- [Definition 14.8](../section-14/section-14-1/180-definition-14-8.md)
- [Theorem 14.26](../section-14/section-14-4/195-theorem-14-26.md)
- [Corollary 16.2](215-corollary-16-2.md)
- [Lemma 16.3](216-lemma-16-3.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 16.2](../../../../../sources/v1/EllipticCurves.md)
