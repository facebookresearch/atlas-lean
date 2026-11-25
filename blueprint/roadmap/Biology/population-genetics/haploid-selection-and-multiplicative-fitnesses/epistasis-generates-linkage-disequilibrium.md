# Haploid selection and the crossproduct ratio: epistasis generates linkage disequilibrium

Consider haplotypes $AB$, $Ab$, $aB$, $ab$ of two biallelic loci in an infinite haploid population, with
frequencies $x_1, x_2, x_3, x_4 \ge 0$ summing to $1$, positive fitnesses $w_1, w_2, w_3, w_4$ and mean
fitness $\bar w = \sum_i x_i w_i$. [Haploid selection](../natural-selection-fisher-s-theorem-and-the-price/select.md) without recombination gives $x_i' = x_i w_i / \bar w$, so
the [linkage disequilibrium](../linkage-disequilibrium-and-haldane-s-map-functio/linkage-diseq.md) $D = x_1 x_4 - x_2 x_3$ becomes

$$D' = \frac{x_1 x_4\, w_1 w_4 - x_2 x_3\, w_2 w_3}{\bar w^{\,2}},$$

and, when $x_2 x_3 > 0$, the crossproduct ratio $R = x_1 x_4 / (x_2 x_3)$ becomes
$R' = R \cdot w_1 w_4 / (w_2 w_3)$. In particular, starting from linkage equilibrium with allele
frequencies $p_A = x_1 + x_2$, $p_B = x_1 + x_3$, $p_a = 1 - p_A$ and $p_b = 1 - p_B$ (so $x_1 x_4 = x_2 x_3 = p_A p_a p_B p_b$),

$$D' = \frac{p_A p_a p_B p_b \,(w_1 w_4 - w_2 w_3)}{\bar w^{\,2}} .$$

So selection keeps linkage equilibrium exactly when the fitnesses are multiplicative across loci
($w_1 w_4 = w_2 w_3$) or a locus is monomorphic; otherwise it creates disequilibrium of the sign of
$w_1 w_4 - w_2 w_3$. The multiplicative case also follows, at recombination fraction $0$, from
[Multiplicative haploid selection preserves linkage equilibrium](recombine-select-eq-mul.md). Writing $w_1 = (1 + s)(1 + t)(1 + E)$, $w_2 = 1 + s$, $w_3 = 1 + t$, $w_4 = 1$, the
factor is $w_1 w_4 / (w_2 w_3) = 1 + E$, so the epistasis $E$ measures departure from multiplicative
fitness; additive fitnesses ($E = -st/((1 + s)(1 + t))$, so $E < 0$ when $st > 0$) create negative
disequilibrium from linkage equilibrium when both loci are polymorphic.

## Depends on

- [One generation of haploid selection](../natural-selection-fisher-s-theorem-and-the-price/select.md)
- [Linkage disequilibrium of a two-locus gamete law](../linkage-disequilibrium-and-haldane-s-map-functio/linkage-diseq.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VIII.2 "A Haploid 2-locus Model", equations (VIII-3)–(VIII-9), pp. 360–361.
