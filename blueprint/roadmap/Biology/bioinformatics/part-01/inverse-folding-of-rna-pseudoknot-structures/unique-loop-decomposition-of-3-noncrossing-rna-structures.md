# Unique loop decomposition of 3-noncrossing RNA structures

**Setting.** A $3$-noncrossing RNA structure on $[n]$ is a diagram of arcs $(i,j)$, $i<j$, with vertex degrees at most $1$, no arcs $(i,i+1)$, and no three mutually crossing arcs. Pairs of crossing arcs are allowed, which produces H-type and kissing-hairpin pseudoknots. Order arcs by nesting: $\alpha' = (i',j') \prec \alpha = (i,j)$ iff $i < i' < j' < j$. For an arc $\beta$, let $\mathscr{A}_S(\beta)$ be the set of arcs crossing $\beta$. An arc $\alpha\in\mathscr{A}_S(\beta)$ is **minimal $\beta$-crossing** if no $\alpha'\in\mathscr{A}_S(\beta)$ satisfies $\alpha'\prec\alpha$.

**Loop types.**

1. *Hairpin loop:* an arc $(i,j)$ together with the interval $[i+1, j-1]$.
2. *Interior loop:* $\big((i_1,j_1), [i_1+1, i_2-1], (i_2,j_2), [j_2+1, j_1-1]\big)$ with $(i_2,j_2)$ nested in $(i_1,j_1)$.
3. *Multi-loop:* a sequence $\big((i_1,j_1),[i_1+1,\omega_1-1],S_1,[\tau_1+1,\omega_2-1],S_2,\dots,S_k,[\tau_k+1,j_1-1]\big)$, where each $S_h$ is a $3$-noncrossing substructure over $[\omega_h,\tau_h]$ nested in $(i_1,j_1)$, which may itself contain crossing arcs (a pseudoknot structure), and where, if every $S_h$ is a single arc $(\omega_h,\tau_h)$, then $k\ge2$ (the source's Section 2.1, item (3)).
4. *Pseudoknot:* a set of arcs $P = \{(i_1,j_1),\dots,(i_t,j_t)\}$ with $i_1 = \min i_h$ and $j_t = \max j_h$. Its crossing (dependency) graph must be connected, so the induced diagram is irreducible, and each $(i_h, j_h)$ must be minimal $\beta$-crossing for some arc $\beta$. The pseudoknot also contains every vertex $i_1 < x < j_t$ that does not lie in a hairpin, interior or multi-loop.

**Theorem.** Every $3$-noncrossing RNA pseudoknot structure has a unique decomposition into hairpin loops, interior loops, multi-loops and pseudoknots.

## Expansion

Uniqueness is what makes loop-based free energies well defined for pseudoknotted structures. The energy of a structure is the sum of the energies of its loops, which extends the Turner nearest-neighbour model, so minimum-free-energy folding over $3$-noncrossing, $\sigma$-canonical structures (all stacks of length at least $\sigma \ge 3$) can be done by dynamic programming over motifs and skeleta. The inverse-folding algorithm **Inv** builds on this decomposition. Given a target $3$-noncrossing structure $T$, it searches for a sequence $s$ whose minimum-free-energy fold is $T$. It generates compatible candidate sequences and refines them by local search over the loop decomposition, using the structure distance (the number of positions paired differently) between the target and the current fold. The sequences it finds lie in the neutral network of $T$, the set of sequences folding into $T$.

## Depends on

- [Exponential growth rate of k-noncrossing RNA structures](../asymptotic-enumeration-of-k-noncrossing-rna-structures/exponential-growth-rate-of-k-noncrossing-rna-structures.md)

## Sources

- J. Z. M. Gao, L. Y. M. Li and C. M. Reidys, "Inverse Folding of RNA Pseudoknot Structures", arXiv:1003.2015 (2010), Section 2 (loop types, pseudoknot definition and Theorem 1) and Section 3 (the algorithm), <https://doi.org/10.48550/arXiv.1003.2015>.
