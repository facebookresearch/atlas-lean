# Z-relations and delta rules for incremental maintenance

A $\mathbb{Z}$-relation is a finitely supported function from tuples to $\mathbb{Z}$. Under pointwise
addition $\mathbb{Z}$-relations form an abelian group; bags and sets embed as $\mathbb{Z}$-relations with
nonnegative, respectively $\{0,1\}$-valued, multiplicities. Selection, projection and union are linear
(group homomorphisms), so for such an operator $Q$ and a change $\Delta R$,
$Q(R + \Delta R) - Q(R) = Q(\Delta R)$. Natural join is bilinear:

$$(R + \Delta R) \bowtie (S + \Delta S) - R \bowtie S = \Delta R \bowtie S + R \bowtie \Delta S + \Delta R \bowtie \Delta S.$$

Duplicate elimination is not linear.

## Depends on

- [K-relations and positive relational algebra over a semiring](k-relations-and-positive-relational-algebra-over-a-semiring.md)

## Sources

- M. Budiu, F. McSherry, L. Ryzhyk and V. Tannen, *DBSP: Automatic incremental view maintenance for rich query languages*, VLDB 2023, arXiv:2203.16684, §4.1 and Definition 4.3. <https://arxiv.org/pdf/2203.16684>
