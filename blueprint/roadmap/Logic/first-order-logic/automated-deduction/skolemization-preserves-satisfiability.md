# Skolemization preserves satisfiability

*Skolemization* $\Rightarrow_S$, applied only at the top of a prenex formula, rewrites $\forall x_1 \dots \forall x_n\, \exists y\, F$ to $\forall x_1 \dots \forall x_n\, F\{y \mapsto f(x_1, \dots, x_n)\}$ for a new function symbol $f$ of arity $n$ (a Skolem function). Structures have nonempty universes, as for the prenex transformation.

Let $F$ be a closed formula over a signature $\Sigma$, let $G$ be a prenex form of $F$ produced by [the prenex transformation](prenex-transformation-preserves-equivalence.md) $F \Rightarrow_P^* G$, so that $F$ and $G$ are equivalent, and let $G \Rightarrow_S^* H$ with $H$ in prenex form without existential quantifiers, over $\Sigma'$, the extension of $\Sigma$ by the Skolem functions. Then

1. $H \models G$, but in general $G \not\models H$;
2. $G$ is satisfiable over $\Sigma$ if and only if $H$ is satisfiable over $\Sigma'$.

## Depends on

- [Prenex transformation preserves equivalence](prenex-transformation-preserves-equivalence.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.5, Skolemization and Theorem 3.9 (ii) and (iii), p. 56.
