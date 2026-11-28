# Concept satisfiability in ALC with inverse roles in value restrictions and number restrictions on compositions and inverses is undecidable

Adding to the description logic ALC number restrictions on role compositions is harmless, but also allowing inverse roles both in number and in value restrictions makes concept satisfiability undecidable.

**Logics.** Concepts of [ALC](../alc-syntax-semantics-and-reasoning-tasks.md) are built from concept names with $\top$, $\bot$, $\neg$, $\sqcap$, $\sqcup$ and the value restrictions $\forall R.C$ and $\exists R.C$. *Number restrictions* ${\ge}n\,R$ and ${\le}n\,R$, for $n\in\mathbb N$, hold at an individual $i$ when $i$ has at least, respectively at most, $n$ distinct $R$-successors; *qualified* number restrictions ${\ge}n\,R.C$ and ${\le}n\,R.C$ count only successors in $C$. Complex roles are built from role names $P$ by the inverse $R^-$, interpreted as $\{(i,j):(j,i)\in R^{\mathcal I}\}$, and the composition $R\circ S$, interpreted as $\{(i,j):\exists k\,(i,k)\in R^{\mathcal I},(k,j)\in S^{\mathcal I}\}$. For a set $M$ of role constructors:

- $\mathcal{ALCN}(M)$ allows complex roles built with $M$ in number restrictions only, value restrictions using role names;
- $\mathcal{ALC\bar N}(M)$ allows such complex roles both in value restrictions and in number restrictions;
- $\mathcal{ALCQ}(M)$ allows them in qualified number restrictions, which also express value restrictions.

Thus $\mathcal{ALCN}(M)\subseteq\mathcal{ALC\bar N}(M)\subseteq\mathcal{ALCQ}(M)$ in expressive power. A concept $C$ is *satisfiable* if $C^{\mathcal I}\neq\emptyset$ in some interpretation $\mathcal I$.

**Theorem (Grandi).** Concept satisfiability, and hence subsumption, is undecidable for $\mathcal{ALC\bar N}(\circ,{}^-)$ and for $\mathcal{ALCQ}(\circ,{}^-)$.

On the other side of the boundary, concept satisfiability is decidable for $\mathcal{ALCQ}(\circ)$, by a tableau algorithm given in the same paper (its Theorem 2 covers an extension with unions and intersections of role chains of equal length), and hence for $\mathcal{ALC\bar N}(\circ)$ and $\mathcal{ALCN}(\circ)$; the decidability of $\mathcal{ALCN}(\circ)$ and the undecidability of $\mathcal{ALCN}(\circ,\sqcap)$ and $\mathcal{ALCN}(\circ,{}^-,\sqcup)$ are due to Baader and Sattler. Decidability of $\mathcal{ALCN}(\circ,{}^-)$, with compositions and inverses only in number restrictions, is left open in the source (Sections 1 and 4).

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the domino problem for the plane: given domino types $D$ with horizontal and vertical matching relations $H,V\subseteq D\times D$, is there a tiling $t:\mathbb Z\times\mathbb Z\to D$ with $(t(m,n),t(m+1,n))\in H$ and $(t(m,n),t(m,n+1))\in V$ for all $m,n$? From a tiling system $\mathcal D$ one builds a concept $E_{\mathcal D}$ that is satisfiable exactly when $\mathcal D$ has a compatible tiling. The grid consists of grid points and centers of grid squares, each center joined to the four vertices of its square by a role $R$; nine disjoint types of points and of centers, together with number restrictions on compositions such as $R\circ R^-$, force the squares to fit together into a grid isomorphic to $\mathbb Z\times\mathbb Z$. Atomic concepts for the domino types and value restrictions express local compatibility, and an auxiliary role $U$ from a start individual to every center, so that $U\circ R$ reaches every grid point, lets value restrictions impose the tiling conditions everywhere.

## Sources

- F. Grandi, "On expressive description logics with composition of roles in number restrictions", in *Logic for Programming, Artificial Intelligence, and Reasoning (LPAR 2002)*, Lecture Notes in Computer Science 2514, pp. 202–215, Springer, 2002, doi:[10.1007/3-540-36078-6_14](https://doi.org/10.1007/3-540-36078-6_14) (the conference paper, whose abstract states both results); read in the extended version arXiv:cs/0308029v1 ([arXiv](https://arxiv.org/abs/cs/0308029v1)), whose numbering is used: the syntax and semantics figure and the inclusions in the introduction, the domino problem and Theorem 1 in the section "Undecidability of ALC N̄(∘,⁻)", and Theorem 2 in the section "Decidability of ALCQ(∘)".
