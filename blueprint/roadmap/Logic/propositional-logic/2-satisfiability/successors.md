# Successors in the implication graph

Let $\varphi$ be a CNF formula and $l$ a literal
over the variables of $\varphi$, and write $\neg l$ for the complementary literal. The
successors of $l$ are the literals $m$ over the variables of $\varphi$ such that the
implication graph of $\varphi$ has an edge from $l$ to $m$: some clause of $\varphi$ contains
$\neg l$ and $m$, either as two different literals or as its only literal. They are listed
without repetition, in the order of the list of all literals over the variables of $\varphi$.
