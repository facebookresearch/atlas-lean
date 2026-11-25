# Cells after sentinel deletion

Let $S$ be a node store and $x$ an address whose cell
holds a node with previous address $p$ and next address $n$, where the cells at $p$ and $n$ are
nonempty. For every address $z$, let $C$ be the cell of $S$ at $z$ if $z \ne p$, and that cell
with its next address set to $n$ if $z = p$. Then after sentinel deletion of $x$ from $S$ the
cell at $z$ is $C$ if $z \ne n$, and $C$ with its previous address set to $p$ if $z = n$.
