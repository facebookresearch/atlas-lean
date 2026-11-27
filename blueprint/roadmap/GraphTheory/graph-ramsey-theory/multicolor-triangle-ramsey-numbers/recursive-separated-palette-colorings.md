# Recursive separated-palette colorings

Fix an alphabet of size $H\ge2$ and let $w=\lceil 2H\log H\rceil$, $s=w(w+1)+1$, and $a=\max(2,\lceil\log H\rceil)$. The stage allocates $K(H)=Has$ colors. Within a copy of an old complete graph, relabel its colors using the palette assigned to the copy; between copies color edges using the palette differences and a coordinate-covering map on alphabet strings. The stage construction keeps each color graph $j$-colorable after stage $j\le H$ as well as triangle-free. A family of equal-cardinality palettes is separated at level $s$ when $|P\setminus Q|\ge s$ for any two distinct palettes. For maps $f,g$ from length-$s$ strings to length-$s$ strings on the alphabet, coordinate covering means that for any strings $x,y$, either $x_i=f(y)_i$ for some coordinate $i$, or $y_i=g(x)_i$ for some coordinate $i$. The saturation condition on an $s$-row array with the length-$w$ strings as columns requires that any set of $w+1$ columns has a row displaying every alphabet symbol on the set.

## Expansion

Separate the matrix saturation, separated-palette family, coordinate-covering maps, and recursive coloring into their own definitions and state the exact disjointness and colorability invariants. The recursion cannot be replaced by the existence of some finite Ramsey number.

## Sources

- [Stage construction and palette usage](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L1297-L1367)
- [Matrix width and row count](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L1852-L1867)
- [Stage color count](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2241-L2245)
