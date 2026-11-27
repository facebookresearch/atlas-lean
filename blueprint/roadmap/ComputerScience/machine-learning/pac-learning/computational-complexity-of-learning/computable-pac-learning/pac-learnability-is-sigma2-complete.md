# PAC learnability is Σ⁰₂-complete for a computable family

There is a computable family of hypothesis classes for which the set of indices of PAC learnable classes is $\Sigma^0_2$-complete, and $\Sigma^0_2$ is an upper bound for every computable family. Since PAC learnability means finite VC dimension, the same holds for finiteness of the VC dimension.

**Setting.** Hypotheses are total computable functions $\mathbb{N} \to \{0,1\}$. A *computable family* of hypothesis classes is a sequence $(\mathcal{H}_j)_{j \in \mathbb{N}}$ for which a single algorithm, given $j$, enumerates (indices of) the members of $\mathcal{H}_j$. PAC learnability is agnostic and proper, with no computability requirement on the learner.

**Theorem (Schaefer; Sterkenburg).**

1. For every computable family $(\mathcal{H}_j)_j$ the index set $\{ j : \mathcal{H}_j \text{ is PAC learnable} \}$ is in $\Sigma^0_2$.
2. There is a computable family $(\mathcal{H}_j)_j$ for which this index set is $\Sigma^0_2$-complete.

## Depends on

- [Learners and agnostic PAC learnability](../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)
- [The arithmetical class Σₙ](../../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)

## Proof depends on

- [Fundamental theorem of statistical learning (binary, 0-1 loss)](../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/fundamental-theorem-of-statistical-learning.md)

## Expansion

By the fundamental theorem of PAC learning, $\mathcal{H}$ is PAC learnable if and only if $\mathrm{VCdim}(\mathcal{H}) < \infty$. The condition $\mathrm{VCdim}(\mathcal{H}) < d$ reads: for all distinct $x_1, \dots, x_d$ there are labels $y_1, \dots, y_d$ such that for all $h \in \mathcal{H}$ some $h(x_i) \ne y_i$. Only the first and third quantifiers are unbounded, so this is $\Pi^0_1$ uniformly in $d$ and the index, and $\exists d$ makes finiteness $\Sigma^0_2$.

For hardness, let $(h_i)_i$ be a computable enumeration of the hypotheses with finite support and $(W_j)_j$ the standard enumeration of c.e. sets, and put $\mathcal{H}_j = \{ h_i : i \le |W_j| \}$ (the set $\{ n : n \le |W_j| \}$ is c.e. uniformly in $j$). If $W_j$ is finite, $\mathcal{H}_j$ is finite and has finite VC dimension; otherwise $\mathcal{H}_j$ contains all finitely supported hypotheses and has infinite VC dimension. Hence the index set equals $\mathrm{Fin} = \{ j : W_j \text{ is finite} \}$, which is $\Sigma^0_2$-complete.

## Sources

- Tom F. Sterkenburg, "On characterizations of learnability with computable learners", Proceedings of the Thirty Fifth Conference on Learning Theory (COLT 2022), Proceedings of Machine Learning Research 178, pp. 3365–3379, 2022; Fact 3 (upper bound), Proposition 4 (completeness, attributed to Schaefer) and Theorem 1 (fundamental theorem) of arXiv:2202.05041v2, <https://arxiv.org/abs/2202.05041v2>.
- Marcus Schaefer, "Deciding the Vapnik–Červonenkis dimension is $\Sigma^p_3$-complete", Journal of Computer and System Sciences 58(1), pp. 177–182, 1999, <https://doi.org/10.1006/jcss.1998.1602>; Theorem 4.1, as cited in the paper above; attribution only (not read), the completeness clause rests on Proposition 4 of the version read of the first source above.
