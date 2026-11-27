# Finite satisfiability of monadic first-order logic with polyadic counting is undecidable

Monadic first-order logic extended with comparisons between the numbers of tuples satisfying two formulas can express Diophantine equations over finite models, so no algorithm decides whether a formula of this logic has a finite model.

**Logic.** Let $\mathcal L^1_\sharp$ be the first-order language with unary predicate symbols and equality, extended by *polyadic counting comparisons* $\sharp_{\mathbf x}\varphi\succsim\sharp_{\mathbf y}\psi$, where $\mathbf x=x_1,\dots,x_n$ and $\mathbf y=y_1,\dots,y_m$ are sequences of variables that may occur in $\varphi$ and $\psi$. In a structure $\mathcal M$ with domain $D$ and assignment $s$,

$$
\mathcal M,s\models\sharp_{\mathbf x}\varphi\succsim\sharp_{\mathbf y}\psi\iff\bigl|\{\mathbf d\in D^n:\mathcal M,s^{\mathbf x}_{\mathbf d}\models\varphi\}\bigr|\ge\bigl|\{\mathbf d\in D^m:\mathcal M,s^{\mathbf y}_{\mathbf d}\models\psi\}\bigr|.
$$

Interpreted over finite structures, the resulting logic is called $\mathsf{MFO}^\phi(\sharp)$.

**Theorem (van Benthem and Icard).** The satisfiability problem for $\mathsf{MFO}^\phi(\sharp)$, deciding whether a given formula of $\mathcal L^1_\sharp$ has a finite model, is undecidable. Moreover, the set of valid sentences of $\mathsf{MFO}^\phi(\sharp)$ is not computably enumerable, so $\mathsf{MFO}^\phi(\sharp)$ is not computably axiomatizable.

The polyadic comparisons are what matter: with counting over single variables only, the monadic logic over finite models expresses only Boolean combinations of linear inequalities between the sizes of regions. The source also recalls Härtig's theorem that the validities of full first-order logic with unary counting are neither $\Pi^1_2$ nor $\Sigma^1_2$.

## Depends on

None.

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Every Diophantine inequality $m_1(\mathbf v)+\dots+m_k(\mathbf v)\ge m'_1(\mathbf v)+\dots+m'_j(\mathbf v)$ between sums of monomials with positive natural coefficients is expressible by a sentence of $\mathsf{MFO}^\phi(\sharp)$ whose finite models correspond to its solutions, the variables $\mathsf v_i$ being read as the sizes $|S_i|$ of unary predicates: a monomial $a\mathsf v_1^{e_1}\cdots\mathsf v_n^{e_n}$ is the number of tuples $(x_0,x_1,\dots)$ with $e_i$ coordinates in $S_i$ and $x_0$ among $a$ fixed distinct elements, and the finitely many small solutions this misses are added by explicit disjuncts. Conjunctions of such inequalities express all Diophantine equations, so a decision procedure for finite satisfiability would decide whether a Diophantine equation has a solution in natural numbers, contradicting the Davis–Putnam–Robinson–Matiyasevich theorem. Satisfiable formulas can be enumerated, so validity, the complement of satisfiability of the negation, is not computably enumerable.

## Sources

- J. van Benthem and T. Icard, "Interleaving logic and counting", *The Bulletin of Symbolic Logic* 29(4), pp. 503–587, 2023, doi:[10.1017/bsl.2023.30](https://doi.org/10.1017/bsl.2023.30); read in arXiv:2507.05219v1 ([arXiv](https://arxiv.org/abs/2507.05219v1)), whose numbering is used: the definition of $\mathcal L^1_\sharp$ in the section "Counting Sequences", Lemma 6 (Diophantine inequalities are expressible) and Propositions 4 and 5, and Theorem 1 (Härtig) for the recalled background.
