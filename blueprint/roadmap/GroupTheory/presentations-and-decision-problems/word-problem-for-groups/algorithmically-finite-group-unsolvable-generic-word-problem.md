# Infinite algorithmically finite groups have unsolvable generic word problem

If $\Gamma$ is an infinite, finitely generated, algorithmically finite group (no algorithm lists infinitely many pairwise distinct elements), then its word problem is unsolvable on every generic set of words, for every finite generating set; Dehn monsters are the first computably presented examples.

A finitely generated group $\Gamma$ is algorithmically finite if no infinite computably enumerable set of words represents pairwise distinct elements of $\Gamma$. For a finite generating set $X$, the word problem of $\Gamma$ is solvable on a set $S$ of words in the free group $\mathbb{F}_X$ if some partial algorithm halts on every input $w \in S$ and, on every input on which it halts (in $S$ or not), correctly says whether $w = 1$ in $\Gamma$; $S$ is generic if the proportion of words of length at most $n$ lying in $S$ tends to $1$, and UB-generic if its upper Banach density $\limsup_{n\to\infty}\max_{\omega\in\mathbb{F}_X}|S\cap\omega B_n|/|B_n|$, with $B_n$ the ball of radius $n$, equals $1$ (Definition 2.1 of the source), equivalently if $S$ contains a translate $\omega_n B_n$ of every ball $B_n$ (Proposition 2.2); every generic set is UB-generic (Remark 2.3). If $\Gamma$ is infinite, finitely generated and algorithmically finite, then it has unsolvable UB-generic word problem, and therefore unsolvable generic word problem, with respect to every finite generating set (Corollary 4.3 of the source, stated in the introduction as Corollary D).

Infinite computably presented algorithmically finite groups (Dehn monsters) exist by Myasnikov and Osin, so these are computably presented groups with unsolvable generic word problem.

## Depends on

- [Solvable word problem](word-problem-solvable.md)
- [Group](../../group-basics/group.md)
- [Recursively presented group](../../orderable-groups/word-problem-for-orderable-groups/is-recursively-presented.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

The source characterizes groups with solvable UB-generic word problem: $\Gamma$ has it with respect to $X$ exactly when there is an infinite computably enumerable sequence of words representing elements of strictly increasing length in $\Gamma$ (Theorem 4.1 of the source, a result without a page here). In an infinite algorithmically finite group no such sequence exists, since it would list infinitely many distinct elements. The source also proves that solvability of the equality problem on squares of UB-generic sets implies solvability of the whole word problem.

## Sources

- A. Carnevale and M. Cavaleri, "Partial word and equality problems and Banach densities", Advances in Mathematics 368 (2020), article 107133, https://doi.org/10.1016/j.aim.2020.107133; read in arXiv:1811.11134v3, whose numbering is used here (Corollary D in the introduction, restated as Corollary 4.3, Definition 2.1, Proposition 2.2, Remark 2.3 and Theorem 4.1 of arXiv:1811.11134v3).
