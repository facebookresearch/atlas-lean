# Unification problem for a modal logic

The unification problem for a modal logic $L$ asks, given a formula $\varphi$, whether some substitution $\sigma$ of formulas for the propositional variables makes $\sigma(\varphi)$ a theorem of $L$. Such a $\sigma$ is a unifier of $\varphi$ in $L$.

Let $L$ be a logic, viewed as a set of formulas of a propositional modal language closed under uniform substitution. A *substitution* is a map $\sigma$ from the propositional variables to formulas of the same language, extended homomorphically to all formulas; nominals and other non-variable atoms, when the language has them, are left unchanged. A formula $\varphi$ is *unifiable* in $L$ when there is a substitution $\sigma$ with $\sigma(\varphi) \in L$, and the *unification problem* for $L$ is the decision problem

$$
\text{given } \varphi, \text{ is there a substitution } \sigma \text{ with } \sigma(\varphi) \in L\,?
$$

For a description logic the same question, posed for two concepts $C$ and $D$ and asking for a substitution of concepts for concept variables that makes $\sigma(C)$ and $\sigma(D)$ equivalent, is called *concept unification*; under the usual translation it is unification of $C \leftrightarrow D$ in the corresponding multimodal logic.

## Depends on

- [Modal formulas](../kripke-semantics/formula.md)

## Proof depends on

None.

## Expansion

For normal modal logics the problem is unification modulo the equational theory of the corresponding variety of Boolean algebras with operators. By results of Rybakov and of Ghilardi, unification and admissibility are decidable for intuitionistic propositional logic and for $\mathbf{K4}$, $\mathbf{GL}$, $\mathbf{S4}$ and $\mathbf{S4.3}$; for $\mathbf{K}$ itself both problems were open when the source was written.

## Sources

- F. Wolter and M. Zakharyaschev, "Undecidability of the unification and admissibility problems for modal and description logics", *ACM Transactions on Computational Logic* 9(4):1–20, 2008, doi:10.1145/1380572.1380574; read as arXiv:cs/0609052v1, <https://arxiv.org/abs/cs/0609052v1>: the definition of the unification problem in Section 2, its extension to nominals in Section 4, and concept unification in Section 5.
