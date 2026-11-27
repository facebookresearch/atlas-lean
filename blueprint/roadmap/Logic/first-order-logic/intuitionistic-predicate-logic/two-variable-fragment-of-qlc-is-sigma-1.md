# The two-variable fragment of the predicate logic of linear frames is Σ⁰₁-complete

The superintuitionistic predicate logic $\mathbf{QLC}$ of linear Kripke frames is undecidable, indeed $\Sigma^0_1$-complete, already for formulas with two individual variables, one binary predicate letter and unary predicate letters, and already for positive formulas.

**Setting.** Formulas are those of the intuitionistic predicate language with $\bot$, $\wedge$, $\vee$, $\to$, $\forall$, $\exists$, without equality, constants or function symbols. They are evaluated in intuitionistic Kripke models over augmented frames, as for [quantified intuitionistic logic](quantified-intuitionistic-logic-qint.md): a partial order $(W, R)$, nonempty domains $D_w$ and monotone interpretations of predicate letters. A frame is *linear* if $R$ is a linear order. $\mathbf{QLC}$ is the set of formulas valid in all models with expanding domains ($uRw \Rightarrow D_u \subseteq D_w$) over linear frames; equivalently, the logic obtained from $\mathbf{QInt}$ by adding all formulas $(\varphi \to \psi) \vee (\psi \to \varphi)$. $\mathbf{QLC.cd}$ is the corresponding logic of linear frames with constant domains. A formula is *positive* if it does not contain $\bot$.

**Theorem (Rybakov).** Restrict the language to two individual variables, a single binary predicate letter and infinitely many unary predicate letters. Then

1. $\mathbf{QLC}$ is $\Sigma^0_1$-complete (Theorem 6.1), and so is $\mathbf{QLC.cd}$ (Corollary 6.3);
2. the positive fragments of $\mathbf{QLC}$ and of $\mathbf{QLC.cd}$ are $\Sigma^0_1$-complete (Corollary 8.4).

More generally, every logic $L$ with $\mathbf{QLC} \subseteq L \subseteq \mathbf{QSIL}(\mathfrak{G} \odot \mathbb{N})$ is $\Sigma^0_1$-hard in this language, where $\mathbf{QSIL}(\mathfrak{G} \odot \mathbb{N})$ is the logic of the frame $\mathfrak{G} = (\mathbb{N}, \leq)$ with constant domain $\mathbb{N}$ (Theorem 6.2).

Since $\mathbf{QLC}$ is the superintuitionistic fragment of the modal predicate logic $\mathbf{QS4.3}$ under the Gödel translation, the result also concerns that fragment.

## Depends on

- [Quantified intuitionistic logic QInt](quantified-intuitionistic-logic-qint.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

For a finite set $T$ of tile types one constructs a two-variable formula $\varphi_T$ such that if some $T$-tiling of $\mathbb{N} \times \mathbb{N}$ exists, $\varphi_T$ is refuted at the root of a model over $\mathfrak{G} \odot \mathbb{N}$, and if none exists, $\varphi_T$ is valid on all frames of $\mathbf{QLC}$. The construction modifies a method of Marx and Reynolds that encodes tilings using natural numbers rather than an enumeration of pairs, and uses a "double labeling" of the elements of the domains so that two individual variables suffice. Membership in $\Sigma^0_1$ holds because $\mathbf{QLC}$ and $\mathbf{QLC.cd}$ are recursively axiomatizable.

## Sources

- M. Rybakov, "Superintuitionistic predicate logics of linear Kripke frames: undecidability with two individual variables", *Annals of Pure and Applied Logic* 177(10), 2026, article 103811, doi:10.1016/j.apal.2026.103811; read as arXiv:2505.00531v2, <https://arxiv.org/abs/2505.00531v2>: Section 2 (syntax and Kripke semantics), Section 1 (equivalent definitions of $\mathbf{QLC}$), Theorems 6.1 and 6.2, Corollaries 6.3 and 8.4 of arXiv:2505.00531v2.
