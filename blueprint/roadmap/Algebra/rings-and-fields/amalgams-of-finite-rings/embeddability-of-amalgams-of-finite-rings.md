# Embeddability of amalgams of finite rings is undecidable

No algorithm decides whether an amalgam of finite rings, finitely many finite rings sharing a common subring, embeds in some ring, or in some finite ring; the same holds for weak embeddings. Every amalgam of finite groups, by contrast, embeds in a finite group.

A *ring amalgam* $[S_i ; U ; \phi_i]$, $i \in I$ with $I$ finite, consists of rings $S_i$, a ring $U$ (the *core*) and injective homomorphisms $\phi_i \colon U \to S_i$; it is *finite* when $I$ and all the rings are finite, and it is given by the operation tables and the maps. An *embedding* of the amalgam in a ring $T$ is a family of injective homomorphisms $\nu_i \colon S_i \to T$ such that for $s \in S_i$ and $t \in S_j$, $\nu_i(s) = \nu_j(t)$ holds exactly when either $i = j$ and $s = t$, or $s = \phi_i(u)$ and $t = \phi_j(u)$ for some $u \in U$. A *weak embedding* only requires injective homomorphisms $\nu_i$ with $\nu_i(\phi_i(u)) = \nu_j(\phi_j(u))$ for all $u \in U$.

**Theorem (Jackson).**

1. There is no algorithm that decides, given a finite ring amalgam, whether it embeds in a ring, and none that decides whether it embeds in a finite ring.
2. The same holds with weak embeddings in place of embeddings.

Conventions: rings are associative and are not required to have an identity element (the proof uses semigroup rings $\mathbb{Z}_2[S]$ of semigroups $S$ without identity); a finite ring amalgam may contain a ring that lies outside a given class, and the source also shows undecidability when the amalgam is restricted to members of the class (the *strong* decision problem) for rings and finite rings. The same statements hold for amalgams of finite semigroups; the source notes that Sapir had obtained Theorem 1.4 earlier by a different method, using Minsky machines.

## Depends on

- [Ring, not necessarily with an identity element](../ring.md)

## Proof depends on

None.

## Expansion

The proof first treats semigroups. Given a finite symmetric partial group $G_1$, the source builds, for each extension $G_4$ of rank four of $G_1$, a semigroup amalgam $A(G_1, G_4)$ of a semigroup $S(G_1, G_4)$ of triples $(i, g, j)$ with the upper half of the Brandt semigroup $B_5(\langle 1 \rangle)$, and proves that $G_1$ embeds in a group (respectively a finite group) exactly when, for some extension $G_4$, the amalgam $A(G_1, G_4)$ embeds, or weakly embeds, in a semigroup (respectively a finite semigroup). Embeddability of finite partial groups in groups and in finite groups is undecidable, as recorded in the survey of Kharlampovich and Sapir cited by the source, and the finitely many extensions of rank four can be listed effectively. Finally, the semigroup amalgam $A = [S_i; U]$ gives the ring amalgam $\mathbb{Z}_2[A] = [\mathbb{Z}_2[S_i]; \mathbb{Z}_2[U]]$: if $A$ (weakly) embeds in a semigroup $T$, then $\mathbb{Z}_2[A]$ (weakly) embeds in $\mathbb{Z}_2[T]$, finite when $T$ is; and a (weak) embedding of $\mathbb{Z}_2[A]$ in a ring $R$ restricts to one of $A$ in the multiplicative semigroup of $R$.

A good expansion adds and links pages for the undecidability of embedding finite partial groups in groups and in finite groups, and for the equivalence between embeddability of $G_1$ and of the amalgams $A(G_1, G_4)$.

## Sources

- Marcel Jackson, *The embeddability of ring and semigroup amalgams is undecidable*, Journal of the Australian Mathematical Society (Series A) 69 (2000), no. 2, 272–286, https://doi.org/10.1017/S1446788700002214; read in the open-access copy at https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D288342F249C1862BA58218B423DDFCA/S1446788700002214a.pdf; clause 1 is Theorem 1.4 and clause 2 Theorem 1.5 there, proved from Theorem 3.1 and the reduction from semigroups to rings in Section 1.
