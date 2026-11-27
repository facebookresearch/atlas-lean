# Mints hierarchy of implicational-universal formulas

The Mints hierarchy stratifies first-order intuitionistic formulas built from implication and universal quantification by the alternation of positive and negative quantifier occurrences, an intuitionistic analogue of the prenex classes $\Sigma_n$ and $\Pi_n$ that needs no prenex form.

**Formulas.** Consider intuitionistic first-order logic without function symbols and without equality, restricted to the $(\forall, \to)$-fragment: a formula is an atom $P(x_1, \dots, x_n)$ with $n \geq 0$ and object variables $x_i$, an implication $\varphi \to \psi$, or $\forall x\,\varphi$. Implication associates to the right.

**Classes.** $\Sigma_0 = \Pi_0$ is the set of quantifier-free formulas, and, with $\mathbf{a}$ ranging over atoms,

$$
\Sigma_{n+1} ::= \mathbf{a} \mid \Pi_n \mid \Pi_{n+1} \to \Sigma_{n+1}, \qquad \Pi_{n+1} ::= \mathbf{a} \mid \Sigma_n \mid \Sigma_{n+1} \to \Pi_{n+1} \mid \forall x\, \Pi_{n+1},
$$

and $\Delta_n = \Sigma_n \cap \Pi_n$. For example $(\forall x\,P(x) \to Q) \to Q \in \Pi_1$, $\forall x(\forall y\,R(y) \to P(x)) \to Q \in \Sigma_2$, and $\forall x\,P(x) \to (\forall y\,R(y) \to Q) \to Q \in \Delta_2$.

**Decision problem.** For a class $C$, the *decision problem for $C$* asks, given a formula of $C$, whether it is provable in intuitionistic first-order logic.

## Depends on

- [Quantified intuitionistic logic QInt](quantified-intuitionistic-logic-qint.md)

## Proof depends on

None.

## Expansion

Every $\Sigma_n$ formula is classically equivalent to a prenex $\Sigma_n$ formula, and similarly for $\Pi_n$, but not conversely in intuitionistic logic: $\forall x(((P(x) \to R(x)) \to P(x)) \to P(x))$ is a classical tautology but is intuitionistically equivalent to no quantifier-free formula. The hierarchy is strict with respect to expressive power. Provability for $\Sigma_1$ is EXPSPACE-complete, and coNEXPTIME-complete when predicate arities are bounded.

## Sources

- Aleksy Schubert, Paweł Urzyczyn and Konrad Zdanowski, "On the Mints hierarchy in first-order intuitionistic logic", *Logical Methods in Computer Science* 12(4):11, 2016, doi:10.2168/LMCS-12(4:11)2016; read as arXiv:1610.02675v3, <https://arxiv.org/abs/1610.02675v3>: Section 2 (the $(\forall,\to)$-fragment) and Section 2.2 (the Mints hierarchy and its strictness) of arXiv:1610.02675v3, with the complexity results of Sections 5 and 6.
