# Component halving in Borůvka's algorithm

Let $C$ be a finite set of component labels and $f \colon C \to C$ a merging map such that every label shares its image with a different label: for each $c \in C$ there is $d \ne c$ with $f(d) = f(c)$. Then

$$2\, |f(C)| \le |C|.$$

No graph or planarity hypothesis is involved. In Borůvka's minimum spanning tree algorithm each component selects an edge to another component, so every merged component contains at least two old ones and the number of components at least halves in each round.
