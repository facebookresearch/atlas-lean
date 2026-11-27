# Two-occurrence vector representation of rooted binary phylogenetic trees

**Trees.** A rooted binary phylogenetic tree on $X = \{1,\dots,n\}$ is a rooted tree with $n$ leaves bijectively labelled by $X$, every non-leaf, non-root node of out-degree $2$, and (for convenience) an extra root node of out-degree $1$ above the top split. There are $(2n-3)!!$ such trees.

**Definition.** A vector $\mathbf v$ over the alphabet $X$ is a *tree representation* if
1. every $i \in X$ occurs exactly twice in $\mathbf v$ (so $\mathbf v$ has length $2n$);
2. $v_1 = 1$;
3. for every $i \in X\setminus\{1\}$, the first occurrence of $i$ precedes the second occurrence of $i-1$;
4. for every $i \in X\setminus\{1\}$, the second occurrence of $i$ follows the second occurrence of $i-1$.

**Theorem.** Tree representations on $X$ are in one-to-one correspondence with rooted binary phylogenetic trees on $X$. In particular there are $(2n-3)!!$ tree representations of length $2n$ (for example $1\,2\,1\,2$ is the only one for $n = 2$, and there are $3, 15, 105$ for $n = 3, 4, 5$).

**HOP rearrangement.** Writing $i$ and $\underline i$ for the first and second occurrence of $i$, a HOP on $i > 1$ moves the first occurrence $i$ to a new position between $v_1 = 1$ and $\underline{i-1}$. Then:
1. every HOP is a subtree prune-and-regraft (SPR) move;
2. for a fixed taxon ordering, the graph on tree representations whose edges are single HOPs is connected, and its diameter is $n$;
3. the HOP neighbourhood of any tree has size quadratic in $n$.

## Proof sketch

Condition 4 forces $\underline{i}$ to come after $\underline{i-1}$, so in a representation of the first $i-1$ taxa the last entry is $\underline{i-1}$, and adding taxon $i$ appends $\underline i$ at the end. Condition 3 then leaves exactly the $2(i-1) - 1 = 2i-3$ gaps strictly between $v_1$ and $\underline{i-1}$ for the first occurrence of $i$. These choices mirror stepwise addition of taxa: a rooted binary tree on $i-1$ taxa (with its root edge) has $2i-3$ edges, and taxon $i$ is attached by subdividing one of them. Matching gap $\leftrightarrow$ edge through the labelling taxon sequences (the clade-size-ordered sequence of node labels on each taxon's root-to-leaf path) gives the encoding and decoding algorithms and the count $\prod_{i=2}^n(2i-3) = (2n-3)!!$. A HOP changes only where one taxon's first occurrence sits, i.e. where its subtree is regrafted, which is why it is an SPR move.

## Sources

- Cedric Chauve, Caroline Colijn and Louxin Zhang, "A vector representation for phylogenetic trees", *Philosophical Transactions of the Royal Society B: Biological Sciences* 380 (2025), 20240226, <https://doi.org/10.1098/rstb.2024.0226>. Preprint version: arXiv:2405.07110 (2024), tree representation definition, representation theorem, labelling taxon sequence proposition and HOP properties proposition, <https://doi.org/10.48550/arXiv.2405.07110>.
