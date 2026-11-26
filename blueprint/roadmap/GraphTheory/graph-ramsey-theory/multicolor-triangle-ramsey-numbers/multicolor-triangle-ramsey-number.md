# Multicolor triangle Ramsey number

For a natural number $k$, $R_k(3)$ is the
least natural number $N$ such that every edge coloring of the complete graph on
$N$ vertices with colors in $\{0,\ldots,k-1\}$ has a monochromatic triangle.
Unused colors are permitted. This is expressed as the infimum in $\mathbb N$
of the set of such $N$. For the empty palette ($k=0$) the value is $2$:
a labeling exists on the edgeless complete graphs on zero and one vertex,
but no labeling exists on the complete graph on two vertices. The universal
condition is therefore vacuous at order two.

## Sources

- R. E. Greenwood and A. M. Gleason, [*Combinatorial Relations and Chromatic Graphs*](https://doi.org/10.4153/CJM-1955-001-4), Canadian Journal of Mathematics 7 (1955), 1–7, §1 and §2, Corollaries 1–3. Taking each target clique size to be three specializes their threshold; the bounds in §2 give finiteness for two or more colors.
- OpenAI, [*Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 9](https://cdn.openai.com/pdf/ten-proofs-oai.pdf), [pinned definition](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/I_MulticolorTriangleRamsey.lean#L8-L16).
