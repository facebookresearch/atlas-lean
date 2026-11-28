# Fluted fragment

The fluted fragment is the part of first-order logic in which the variables of every atom are a contiguous block ending in the most recently quantified variable, and quantifiers bind only that variable; extensions add equality and binary predicates required to be transitive.

**Definition.** Signatures are purely relational: relation symbols of fixed arities, including $0$-ary ones (proposition letters), and no constants or function symbols. Fix the variable sequence $x_1, x_2, \ldots$. The sets $\mathcal{FL}^{[m]}$ ($m \ge 0$) are defined by induction: (i) every non-equality atom $p(x_\ell, \ldots, x_m)$ whose arguments form a contiguous, possibly empty, subsequence $x_\ell, \ldots, x_m$ ending in $x_m$ is in $\mathcal{FL}^{[m]}$; (ii) $\mathcal{FL}^{[m]}$ is closed under Boolean combinations; (iii) if $\varphi \in \mathcal{FL}^{[m+1]}$, then $\exists x_{m+1}\,\varphi$ and $\forall x_{m+1}\,\varphi$ are in $\mathcal{FL}^{[m]}$. The *fluted fragment* is $\mathcal{FL} = \bigcup_{m \ge 0} \mathcal{FL}^{[m]}$, and a *fluted sentence* is a formula of $\mathcal{FL}^{[0]}$. $\mathcal{FL}^m$ is the set of fluted formulas with at most $m$ variables, free or bound (so its predicates have arity at most $m$).

*Extensions.* $\mathcal{FL}_=$ also allows equality atoms $x_{m-1} = x_m$ in $\mathcal{FL}^{[m]}$ for $m \ge 2$. $\mathcal{FL}\,k\mathrm T$ (respectively $\mathcal{FL}_=\,k\mathrm T$) is $\mathcal{FL}$ (respectively $\mathcal{FL}_=$) with $k$ distinguished binary predicates $T_1, \ldots, T_k$ that are required to be interpreted as transitive relations; $\mathcal{FL}^m\,k\mathrm T$ and $\mathcal{FL}^m_=\,k\mathrm T$ are their $m$-variable parts. For a logic $\mathcal L$, $\mathrm{Sat}(\mathcal L)$ asks whether a given sentence has a model, and $\mathrm{FinSat}(\mathcal L)$ whether it has a finite model.

For example, "no student admires every professor", $\forall x_1(\mathrm{student}(x_1) \to \neg\forall x_2(\mathrm{prof}(x_2) \to \mathrm{admires}(x_1, x_2)))$, is a sentence of $\mathcal{FL}^2$. The fluted fragment itself has the finite model property and a decidable satisfiability problem (Purdy; Pratt-Hartmann, Szwast and Tendera); with one transitive relation and equality, satisfiability and finite satisfiability of $\mathcal{FL}^m_=\,1\mathrm T$ remain decidable (Theorem 20 and Corollary 21 of the source).

## Depends on

None.

## Proof depends on

None.

## Expansion

In a Boolean combination all combined formulas have as free variables a suffix of the prefix $x_1, \ldots, x_m$, and only the last variable of that prefix can be quantified; this is the "lining up" of arguments in columns that gives the fragment its name. Proposition letters combine freely with formulas of any $\mathcal{FL}^{[m]}$.

## Sources

- I. Pratt-Hartmann and L. Tendera, "The fluted fragment with transitive relations", *Annals of Pure and Applied Logic* 173(1), 2022, article 103042, <https://doi.org/10.1016/j.apal.2021.103042>; numbers from arXiv:2006.11169v1, <https://arxiv.org/abs/2006.11169v1>: Section 2 (definition of $\mathcal{FL}^{[m]}$, $\mathcal{FL}^m$, $\mathcal{FL}_=$, $\mathcal{FL}\,k\mathrm T$ and $\mathcal{FL}_=\,k\mathrm T$), Theorem 20 and Corollary 21.
