# The superintuitionistic predicate logic of ω is not recursively enumerable

The intuitionistic predicate logic of the single Kripke frame $(\mathbb{N}, \leq)$, with expanding or constant domains, is both $\Sigma^0_1$-hard and $\Pi^0_1$-hard, hence neither recursively enumerable nor co-recursively enumerable, already with two individual variables, one binary and unary predicate letters, and for positive formulas.

**Setting.** Formulas are intuitionistic predicate formulas, without equality, constants or function symbols, evaluated in Kripke models as for [quantified intuitionistic logic](quantified-intuitionistic-logic-qint.md). Let $\mathfrak{G} = (\mathbb{N}, \leq)$. $\mathbf{QSIL}^{e}\mathfrak{G}$ is the set of formulas valid in all models over $\mathfrak{G}$ with expanding domains, and $\mathbf{QSIL}(\mathfrak{G} \odot \mathbb{N})$ the set of formulas valid in all models over $\mathfrak{G}$ with the constant domain $\mathbb{N}$. For a logic $L$, $L^+$ is its positive fragment (formulas without $\bot$).

**Theorem (Rybakov).** Restrict the language to two individual variables, a single binary predicate letter and infinitely many unary predicate letters. Then every logic $L$ with

$$
\mathbf{QSIL}^{e}\mathfrak{G} \subseteq L \subseteq \mathbf{QSIL}(\mathfrak{G} \odot \mathbb{N})
$$

is both $\Sigma^0_1$-hard and $\Pi^0_1$-hard (Theorem 7.3), and so is its positive fragment $L^+$ (Theorem 8.8). In particular the logics of $\omega$ with expanding domains and with constant domains are not recursively enumerable.

## Depends on

- [Quantified intuitionistic logic QInt](quantified-intuitionistic-logic-qint.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [The two-variable fragment of the predicate logic of linear frames is Σ⁰₁-complete](two-variable-fragment-of-qlc-is-sigma-1.md)

## Expansion

$\Sigma^0_1$-hardness follows from the construction for $\mathbf{QLC}$ (Theorem 6.2), since every such $L$ lies between $\mathbf{QLC}$ and $\mathbf{QSIL}(\mathfrak{G} \odot \mathbb{N})$. For $\Pi^0_1$-hardness one uses a different tiling problem, shown $\Sigma^0_1$-hard in the appendix: whether a set $T = \{t_0, \dots, t_n\}$ admits a tiling of $\mathbb{N} \times \mathbb{N}$ with $f(0,0) = t_0$ and with $f(0, j) = t_1$ for all $j$ beyond some $j^\ast$. Formulas of the same fragment, built with the abbreviation $x \preccurlyeq y = Q(y) \to Q(x)$, are refuted in a model over $\mathfrak{G}$ iff such a tiling exists, which uses that every infinite subset of $\omega$ is cofinal (proof of Lemma 7.2; for frames $\langle\alpha, \subseteq\rangle$ the source obtains only $\Sigma^0_1$-hardness, Corollary 6.4); so this $\Sigma^0_1$-hard problem reduces to the complement of $L$.

## Sources

- M. Rybakov, "Superintuitionistic predicate logics of linear Kripke frames: undecidability with two individual variables", *Annals of Pure and Applied Logic* 177(10), 2026, article 103811, doi:10.1016/j.apal.2026.103811; read as arXiv:2505.00531v2, <https://arxiv.org/abs/2505.00531v2>: Section 2, Theorems 6.2, 7.3 and 8.8, Section 7 and the appendix (Section 10) of arXiv:2505.00531v2.
