# Dollo score via the 1-tree

**Setting.** Let $T$ be a rooted binary phylogenetic tree with $n$ leaves and $f$ a binary character (an assignment of states $0/1$ to the leaves). $f$ is a **Dollo-$k$ character** on $T$ if some extension of $f$ to the internal nodes realizes it with at most one $0\to1$ transition (a gain) followed by exactly $k$ transitions $1\to0$ (losses), and $k$ is minimal; this minimal $k=k(f,T)$ is the **Dollo score**. The **1-tree** $\mathcal T(f)$ is the minimum induced subtree of $T$ connecting all leaves in state $1$. Persistent characters (gained at most once and lost at most once) are exactly the Dollo-0 and Dollo-1 characters.

**Theorem.**

*(1)* $0\le k(f,T)\le n-2$.

*(2)* $f$ has a unique Dollo-$k$ labeling: assign state $1$ to the nodes of $\mathcal T(f)$ and $0$ to all others. It can be computed in linear time.

*(3)* If $f$ has at most one leaf in state $1$, then $k(f,T)=0$. Otherwise

$$k(f,T)=\big|\{v\in V(\mathcal T(f)):\deg(v)=2\}\big|-1,$$

where degrees are taken in the subtree $\mathcal T(f)$; equivalently, $k(f,T)$ is the number of maximal $0$-clade roots lying strictly below the most recent common ancestor of the state-$1$ leaves.

*(4)* $f$ is persistent on $T$ if and only if $\mathcal T(f)$ has at most two nodes of degree $2$.

**Contrast with Fitch parsimony.** With $l(f,T)$ the Fitch parsimony score and $\bar f$ the complementary character, $l(f,T)\le\min\{k(f,T),k(\bar f,T)\}+1$, but both differences $|l(f,T)-k(f,T)|$ and $|l(f,T)-k(\bar f,T)|$ can be made arbitrarily large.

## Expansion

In any Dollo realization the unique gain must lie on or above the most recent common ancestor $\mathcal B$ of the state-$1$ leaves, and every node on a path between two state-$1$ leaves must be in state $1$; so the 1-tree is forced to state $1$. Each maximal $0$-clade hanging below $\mathcal B$ then needs a loss on its incoming edge (the "death lemma"), and no other loss is needed. In $\mathcal T(f)$ the top node $\mathcal B$ has degree $2$, and every other degree-2 node has exactly one child outside the 1-tree, whose subtree is one such hanging clade; subtracting the top node gives the formula. Fitch parsimony can use both gains and losses freely, which is why the two scores diverge.

## Sources

- Remco Bouckaert, Mareike Fischer, Kristina Wicke, "Combinatorial perspectives on Dollo-$k$ characters in phylogenetics", arXiv:2011.13479 (2020), Proposition 1, Theorems 1–2, Corollaries 1–3, Propositions 2–3, <https://doi.org/10.48550/arXiv.2011.13479>.
