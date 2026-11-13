# Besicovitch's Kakeya set of measure zero

There is a compact set $K \subseteq \mathbb{R}^2$
of Lebesgue measure zero that contains a unit segment in every direction: $K$ is measurable,
and for every unit vector $v \in \mathbb{R}^2$ there is a point $a \in \mathbb{R}^2$ with
$a + t v \in K$ for all $t \in [0, 1]$.

The proof here follows T. W. Körner, "Besicovitch via Baire", Studia Math. 158 (2003): a
Baire-category argument in the Hausdorff metric space of compact sets, not a Perron-tree
construction.

## Sources

- A. S. Besicovitch, Math. Z. 27 (1928) 312–320 and S. Kakeya, Tohoku Rep. 6 (1917); Perron-tree gives compact measure-zero Kakeya set; Lean states compact Lebesgue-null oriented version in ℝ² with segments `a+t•v`, `t∈[0, 1]`.
