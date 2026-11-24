# Existence of a least finite support

Let $\mathbb{A}$ be an infinite set of atoms and $X$ a set with an action of the group $\mathrm{Perm}_f(\mathbb{A})$ of [finitely supported permutations](fin-perm.md) of $\mathbb{A}$. If a finite set $S_0$ [supports](supports.md) $x \in X$, then some finite set $S \subseteq S_0$ supports $x$ and is contained in every finite support of $x$.

The proof is by strong induction on $S_0$: either every element of $S_0$ lies in every support of $x$, and $S_0$ itself is least, or some $a \in S_0$ is missing from a support $S_a$, and the induction hypothesis applies to the strictly smaller support $S_a \cap S_0$.

## Informally uses

- [Intersection of two supports is a support](inter.md): $S_a \cap S_0$ is a support.
