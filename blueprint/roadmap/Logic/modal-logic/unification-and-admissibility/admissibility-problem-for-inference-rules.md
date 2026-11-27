# Admissibility problem for inference rules

An inference rule $\varphi_1, \dots, \varphi_n / \varphi$ is admissible in a logic $L$ when every substitution that turns all premises into theorems of $L$ also turns the conclusion into a theorem of $L$. The admissibility problem asks to decide this for a given rule.

Let $L$ be a logic closed under uniform substitution, and let substitutions be as for [unification](unification-problem-for-a-modal-logic.md). An *inference rule* is a finite list of formulas $\varphi_1, \dots, \varphi_n, \varphi$, written $\varphi_1, \dots, \varphi_n / \varphi$. It is *admissible* in $L$ when, for every substitution $\sigma$,

$$
\sigma(\varphi_1) \in L, \ \dots, \ \sigma(\varphi_n) \in L \ \Longrightarrow \ \sigma(\varphi) \in L.
$$

The *admissibility problem* for $L$ is to decide, given a rule, whether it is admissible in $L$.

## Depends on

- [Unification problem for a modal logic](unification-problem-for-a-modal-logic.md)

## Proof depends on

None.

## Expansion

For a consistent logic $L$, a formula $\varphi$ is not unifiable in $L$ exactly when the rule $\varphi / \bot$ is admissible in $L$: the rule is admissible iff no substitution makes $\varphi$ a theorem, because $\sigma(\bot) = \bot \notin L$. So the unification problem reduces to the complement of the admissibility problem, and undecidability of unification gives undecidability of admissibility.

## Sources

- F. Wolter and M. Zakharyaschev, "Undecidability of the unification and admissibility problems for modal and description logics", *ACM Transactions on Computational Logic* 9(4):1–20, 2008, doi:10.1145/1380572.1380574; read as arXiv:cs/0609052v1, <https://arxiv.org/abs/cs/0609052v1>: the definition of the admissibility problem in Section 2.
