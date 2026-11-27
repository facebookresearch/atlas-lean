# Twelve spherical points with a fifty-color obstruction

Set $t=\sum_{m\ge0}10^{-(m+1)!}$, $u=(1-t^2)/(1+t^2)$ and $v=2t/(1+t^2)$. From $Q=\{(1,0),(-1,0),(0,1),(0,-1)\}$ form $X=Q\cup RQ\cup R^{-1}Q$, where $R(x,y)=(ux-vy,vx+uy)$. Then $|X|=12$, $X$ is contained in the unit circle, and every $\mathbb R^n$ with $n>0$ admits a coloring with 50 colors avoiding any monochromatic isometric image of $X$. In particular $X$ fails the Ramsey property defined using every positive number of colors.

## Depends on

- The convergent Liouville series, the two opposite plane rotations, and set-based isometric images.

## Proof depends on

- Distinctness and unit norms of the three rotated squares and a uniform 50-color obstruction in every positive dimension.

## Expansion

State the algebraic/number theoretic parameter facts and the exact combinatorial coloring separately, then derive the final non-Ramsey clause. Use $R^{-1}$ rather than replacing both rotated squares by a single orientation.

## Sources

- [Comparator statement: `OAI.GrahamSpherical.full_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GrahamSpherical.lean#L58-L60)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/172.md)
