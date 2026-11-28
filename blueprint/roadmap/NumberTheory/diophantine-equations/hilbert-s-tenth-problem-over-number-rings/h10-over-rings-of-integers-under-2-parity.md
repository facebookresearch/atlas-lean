# Hilbert's tenth problem over every ring of integers is undecidable under the 2-parity conjecture

If, for every number field $K$ and every elliptic curve $E$ over $K$, the $2$-torsion of the Shafarevich–Tate group $Ш(E/K)$ has even $\mathbb{F}_2$-dimension, then Hilbert's tenth problem over the ring of integers of every number field is undecidable.

For a number field $K$, Conjecture $\mathrm{ST}_2(K)$, which the source writes $Ш\mathrm{T}_2(K)$, is the statement:

$$
\dim_{\mathbb{F}_2} Ш(E/K)[2] \ \text{is even for every elliptic curve } E \text{ over } K ,
$$

where $Ш(E/K)$ is the Shafarevich–Tate group of $E$ over $K$ and $Ш(E/K)[2]$ its subgroup of elements killed by $2$.

**Theorem.** Suppose that Conjecture $\mathrm{ST}_2(K)$ holds for every number field $K$. Then for every number field $K$, Hilbert's tenth problem over the ring of integers $\mathcal{O}_K$ is undecidable: no algorithm decides, for a polynomial with coefficients in $\mathcal{O}_K$, whether it has a zero in $\mathcal{O}_K^n$.

Conventions: the hypothesis is used for all number fields at once, not only for the field $K$ in the conclusion. $\mathrm{ST}_2(K)$ follows from the finiteness of $Ш(E/K)$ for all $E$ (the Shafarevich–Tate conjecture), or just of its $2$-primary part, because the Cassels pairing is then a nondegenerate alternating pairing on the finite group $Ш(E/K)[2^\infty]$; the theorem is conditional on it.

The conclusion also holds unconditionally: Alpöge, Bhargava, Ho and Shnidman, and independently Koymans and Pagano, proved that Hilbert's tenth problem over $\mathcal{O}_K$ has a negative answer for every number field $K$, and Koymans and Pagano proved the same for every infinite ring finitely generated over $\mathbb{Z}$.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../../algebraic-number-theory/number-fields-embeddings/ring-of-integers.md)
- [The Shafarevich–Tate group of an elliptic curve over a number field](../../arithmetic-geometry/cassels-tate-pairing/elliptic-tate-shafarevich.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Hilbert's tenth problem over a ring of integers is undecidable given a rank-one elliptic curve](h10-undecidable-given-a-rank-one-elliptic-curve.md)
- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [The halting problem is recognizable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/tm2-recognizable-halting.md)
- [The halting problem is undecidable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Expansion

Mazur and Rubin control the $2$-Selmer rank of quadratic twists over two fields at once. For a cyclic extension $L/K$ of prime degree they show that, if $\mathrm{ST}_2(K)$ holds, some elliptic curve $E$ over $K$ has $\operatorname{rk} E(L) = \operatorname{rk} E(K) = 1$ (Theorem 1.13 of arXiv:0904.3709v3). Poonen's criterion then makes $\mathcal{O}_K$ Diophantine over $\mathcal{O}_L$, and splitting any cyclic extension into a tower of cyclic steps of prime degree extends this to all cyclic extensions. The deduction of the theorem, due to Poonen and Shlapentokh, takes the Galois closure $L$ of $K/\mathbb{Q}$: for each $g \in \operatorname{Gal}(L/\mathbb{Q})$ the extension of $L$ over the fixed field of $g$ is cyclic, so the ring of integers of each such fixed field is Diophantine over $\mathcal{O}_L$. Their intersection is $\mathcal{O}_L^{\operatorname{Gal}(L/\mathbb{Q})} = \mathbb{Z}$, and a finite intersection of Diophantine sets is Diophantine, so $\mathbb{Z}$ is Diophantine over $\mathcal{O}_L$, hence over $\mathcal{O}_K$ by a lemma of Denef and Lipshitz. Matiyasevich's theorem finishes the proof. The proof needs $\mathrm{ST}_2$ only for the subfields of the Galois closure of $K/\mathbb{Q}$ (Theorem 8.1 of arXiv:0904.3709v3).

By a theorem of Eisenträger, the same hypothesis gives a negative answer to Hilbert's tenth problem over every infinite ring that is finitely generated over $\mathbb{Z}$ (Corollary 1.14 of arXiv:0904.3709v3); this conclusion also holds unconditionally, by Koymans and Pagano.

A good expansion adds and links pages for Mazur and Rubin's rank result for cyclic extensions of prime degree (Theorem 1.13 of arXiv:0904.3709v3), Poonen's criterion from a rank-one elliptic curve, the Denef–Lipshitz lemma passing Diophantine definitions from $\mathcal{O}_L$ to $\mathcal{O}_K$, and the Poonen–Shlapentokh reduction over the Galois closure.

## Sources

- Barry Mazur and Karl Rubin, *Ranks of twists of elliptic curves and Hilbert's tenth problem*, Invent. Math. 181 (2010), no. 3, 541–575, https://doi.org/10.1007/s00222-010-0252-0. Theorem 1.2 of arXiv:0904.3709v3 is the main statement; Conjecture $\mathrm{ST}_2(K)$ is stated in Section 1 of that version.
- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; Theorem 5.2 and Corollary 5.3 of arXiv:1309.0441v1 state a variant, with the weak Shafarevich–Tate conjecture assumed for elliptic curves over $K$ only and an elliptic curve over $\mathbb{Q}$ with $\operatorname{rk} E(\mathbb{Q}) = \operatorname{rk} E(K) = 1$.
- Levent Alpöge, Manjul Bhargava, Wei Ho and Ari Shnidman, *Rank stability in quadratic extensions and Hilbert's tenth problem for the ring of integers of a number field*, Invent. Math. 243 (2026), no. 3, 1129–1139 (published online 2025), https://doi.org/10.1007/s00222-025-01392-3; the unconditional result over $\mathcal{O}_K$ is Corollary 1.2 of arXiv:2501.18774v1, the version read.
- Peter Koymans and Carlo Pagano, *Hilbert's tenth problem via additive combinatorics*, J. Amer. Math. Soc. 40 (2026), no. 1, 195–234, https://doi.org/10.1090/jams/1081; the unconditional results are Theorems 1.1 and 1.2 of arXiv:2412.01768v3, the version read.
- Anwesh Ray and Tom Weston, *Diophantine stability for elliptic curves on average*, European J. Math. 11 (2025), no. 4, article 78, https://doi.org/10.1007/s40879-025-00872-3; Section 1.3 of arXiv:2304.09742v3 records both unconditional proofs.
