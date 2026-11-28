# Which finitely based semigroup varieties have decidable uniform word problem for their finite members

For a semigroup variety defined by finitely many identities in n variables, the uniform word problem for its finite members is decidable exactly when the Zimin word with n+1 letters is not an isoterm for the identities and the variety is periodic or avoids three explicit small semigroups.

**Theorem (Sapir).** Let $\Sigma$ be a finite set of identities in $n$ variables defining a variety $\mathcal V$ of semigroups, and let $\mathcal V_{\mathrm{fin}}$ be the class of finite semigroups in $\mathcal V$ (see [semigroup varieties, isoterms and Zimin words](semigroup-varieties-isoterms-and-zimin-words.md)). The following are equivalent:

1. the uniform word problem for $\mathcal V_{\mathrm{fin}}$ is decidable;
2. the Zimin word $Z_{n+1}$ is not an isoterm for $\Sigma$, and either $\mathcal V$ is periodic, or $\mathcal V$ contains none of the semigroups $T$, $\overrightarrow P^1 \times \overleftarrow P$ and $\overrightarrow P \times \overleftarrow P^1$.

In all other cases the uniform word problem for $\mathcal V_{\mathrm{fin}}$ is undecidable; for the variety of all semigroups this is [Gurevich's theorem](../algorithmic-problems-for-finite-semigroups/uniform-word-problem-for-finite-semigroups.md).

## Depends on

- [Semigroup varieties, isoterms and Zimin words](semigroup-varieties-isoterms-and-zimin-words.md)
- [Semigroup presentations and the word problem](../decision-problems-in-semigroups/semigroup-presentations-and-the-word-problem.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The uniform word problem for finite semigroups is undecidable](../algorithmic-problems-for-finite-semigroups/uniform-word-problem-for-finite-semigroups.md)
- [Which non-periodic semigroup varieties contain finitely presented semigroups with undecidable word problem](word-problem-in-non-periodic-semigroup-varieties.md)

## Expansion

For the implication from 1 to 2, if $\mathcal V$ contains one of $\mathcal M_1$, $\overrightarrow{\mathcal M_2}$, $\overleftarrow{\mathcal M_2}$, Minsky-machine semigroups with an extra counter subgroup show that the quasi-identities holding in $\mathcal V_{\mathrm{fin}}$ are inseparable from those holding in all periodic semigroups of $\mathcal V$, as in Gurevich's theorem; if $Z_{n+1}$ is an isoterm, a substitution $\phi$ with every $\phi^s(x_1)$ an isoterm (Sapir) gives another simulation. For the converse, a periodic $\mathcal V$ has the restricted Burnside property (via Zelmanov's solution of the restricted Burnside problem), so its finite $k$-generated members can be listed, and a non-periodic $\mathcal V$ avoiding the three semigroups has residually finite finitely presented members by the theorem on non-periodic varieties. A good expansion links Zelmanov's theorem, the restricted Burnside property of periodic varieties, the isoterm substitution and Mal'cev's residual finiteness of finitely generated linear semigroups.

## Sources

- Mark Sapir, "Minsky Machines and Algorithmic Problems", in *Fields of Logic and Computation II*, Lecture Notes in Computer Science 9300, Springer, 2015, pp. 273–292, doi:[10.1007/978-3-319-23534-9_17](https://doi.org/10.1007/978-3-319-23534-9_17); read in arXiv:1504.07736v1 ([arXiv](https://arxiv.org/abs/1504.07736v1)), whose numbering is used: Theorem 5.1 and its proof in Section 5.
- Mark V. Sapir, "Weak word problem for finite semigroups", in *Monoids and Semigroups with Applications* (Berkeley, 1989), World Scientific, 1991, pp. 206–219 (cited beside the survey read; not read here).
