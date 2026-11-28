# Footprints of local functions

The local limit of a local function at a state is the bound that locality imposes from all strictly smaller states; a footprint is a state where the function's outcome is strictly below this limit. Smallest safe states are footprints, but in the standard stack-and-heap model they need not be the only ones.

Let $(\Sigma, \bullet, u)$ be a [separation algebra](../abstract-separation-logic/separation-algebras.md), write $\sigma' \prec \sigma$ for $\sigma' \preceq \sigma$ with $\sigma' \neq \sigma$, and for $\sigma' \preceq \sigma$ let $\sigma - \sigma'$ be the unique state with $(\sigma - \sigma') \bullet \sigma' = \sigma$, unique by cancellativity. For $f : \Sigma \to P(\Sigma)^\top$ and a set $A \subseteq \Sigma$, the *local limit imposed by* $A$ and the *local limit* of $f$ are

$$L_{A,f}(\sigma) = \bigsqcap_{\sigma' \preceq \sigma,\ \sigma' \in A} \{\sigma - \sigma'\} \ast f(\sigma'), \qquad L_f(\sigma) = \bigsqcap_{\sigma' \prec \sigma} \{\sigma - \sigma'\} \ast f(\sigma'),$$

meets taken in $P(\Sigma)^\top$, so that an empty meet, as for $L_f(u)$, is $\top$. Then $f$ is a [local action](../abstract-separation-logic/local-actions.md) if and only if $f(\sigma) \sqsubseteq L_f(\sigma)$ for every $\sigma$. For a local $f$, a state $\sigma$ is a *footprint* of $f$, written $F_f(\sigma)$, if $f(\sigma) \sqsubset L_f(\sigma)$ strictly, and $F(f)$ is the set of footprints; a set $A$ is a *basis* for $f$ if $L_{A,f} = f$, and $\Sigma$ itself is always one.

Every smallest safe state of $f$, a state $\sigma$ with $f(\sigma) \neq \top$ and $f(\sigma') = \top$ for all $\sigma' \prec \sigma$, is a footprint, since then $L_f(\sigma) = \top$.

## Depends on

- [Local actions](../abstract-separation-logic/local-actions.md)
- [Separation algebras](../abstract-separation-logic/separation-algebras.md)

## Proof depends on

- [Local actions](../abstract-separation-logic/local-actions.md)

## Expansion

Examples from the source: in the plain heap model the footprints of disposal of a location $l$ are exactly the one-cell heaps $l \mapsto v$. In the stack-and-heap model, for the command $\mathrm{AD}$ that allocates a cell, assigns its address to $x$ and deallocates it, the footprints are the states $x \mapsto v$, its smallest safe states, and also the states $l \mapsto v_1 \bullet x \mapsto v_2$: on the latter $\mathrm{AD}$ cannot leave $x = l$, an outcome its local limit allows, while on a state with $x$ and two or more heap cells the outcome equals the local limit. If $f$ is local then $f(\sigma) \sqsubseteq \{\sigma - \sigma'\} \ast f(\sigma')$ for each $\sigma' \prec \sigma$, hence $f(\sigma) \sqsubseteq L_f(\sigma)$; conversely, for $\sigma_1 \bullet \sigma_2$ with $\sigma_1 \neq u$ the state $\sigma_2$ is a strict substate, and the case $\sigma_1 = u$ is trivial. A non-footprint is a state on which $f$ is determined by its action on smaller states and locality, which is why footprints are the states every complete specification must mention ([footprints are exactly the essential states of complete specifications](essentiality-of-footprints.md)). For $\mathrm{AD}$ on $l \mapsto v_1 \bullet x \mapsto v_2$, the local limit is $\{l \mapsto v_1 \bullet x \mapsto w : w \in L\}$ while the outcome excludes $w = l$; on states with two or more cells the outcome equals the local limit. Missing prerequisite: the stack-and-heap model with variables as resource, defined in the source's Example 2.8.

## Sources

- M. Raza and P. Gardner, "Footprints in local reasoning", *Logical Methods in Computer Science* 5(2:4), 2009, <https://doi.org/10.2168/LMCS-5(2:4)2009>, arXiv:0903.1032v2 <https://arxiv.org/abs/0903.1032v2>, Section 2.1, Lemma 2.3 and Example 2.8; Section 4, Definitions 4.1 and 4.3, Proposition 4.2, Lemma 4.4 and Examples 4.5 and 4.6; Section 5.1, Definitions 5.1 and 5.2 (numbers from arXiv:0903.1032v2).
