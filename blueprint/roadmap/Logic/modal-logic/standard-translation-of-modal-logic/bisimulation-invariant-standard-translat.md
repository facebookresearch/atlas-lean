# Modal formulas are bisimulation-invariant under the standard translation

For every
modal formula $\varphi$, its standard translation $ST_x(\varphi)$ (the first-order formula over
the modal language whose single variable $x$ stands for the current world) is
bisimulation-invariant: for all Kripke models $M$ and $N$, every bisimulation $Z$ between $M$
and $N$ and all worlds $w$ of $M$ and $v$ of $N$ with $Z(w, v)$, the formula $ST_x(\varphi)$
holds in $M$ at $x = w$ if and only if it holds in $N$ at $x = v$.
