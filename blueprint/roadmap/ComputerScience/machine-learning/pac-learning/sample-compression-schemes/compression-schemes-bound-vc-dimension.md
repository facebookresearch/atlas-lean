# Sample compression schemes bound the VC dimension

If a class $C$ of functions $X \to \{0,1\}$ has a sample compression scheme of size $k$ and shatters a finite set $W$, then

$$
2^{|W|} \le (2|W| + 1)^{k}.
$$

In particular a binary class with a finite-size compression scheme has finite VC dimension. No measurability assumption is involved.

## Proof sketch

Run the scheme on the $2^{|W|}$ samples listing the points of $W$ with each labeling. The reconstruction recovers the labeling from a list of at most $k$ labelled points of $W$, so the labelings inject into such lists, of which there are at most $(2|W|+1)^k$.

## Depends on

- [Labelled sample compression scheme](labelled-sample-compression-scheme.md)
- [The VC dimension is at most the size of the ground set](../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Sources

- N. Littlestone and M. K. Warmuth, "Relating Data Compression and Learnability", unpublished manuscript, 1986.
- S. Floyd and M. K. Warmuth, "Sample Compression, Learnability, and the Vapnik-Chervonenkis Dimension", Machine Learning, 1995.
