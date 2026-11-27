# Skolemization preserves satisfiability

A formula is in *prenex form* $Q_1 x_1 \dots Q_n x_n\, F$ if $F$ is quantifier-free and each $Q_i \in \{\forall, \exists\}$. The prenex transformation $\Rightarrow_P$ rewrites, at any position of a formula $H$, $F \leftrightarrow G$ to $(F \to G) \wedge (G \to F)$, $\neg Q x\, F$ to $\bar Q x\, \neg F$, $(Q x\, F) \circ G$ to $Q y\,(F\{x \mapsto y\} \circ G)$ for $\circ \in \{\wedge, \vee\}$, $(Q x\, F) \to G$ to $\bar Q y\,(F\{x \mapsto y\} \to G)$, and $F \circ (Q x\, G)$ to $Q y\,(F \circ G\{x \mapsto y\})$ for $\circ \in \{\wedge, \vee, \to\}$, where $y$ is a fresh variable and $\bar Q$ is the quantifier dual to $Q$. *Skolemization* $\Rightarrow_S$, applied only at the top of a prenex formula, rewrites $\forall x_1 \dots \forall x_n\, \exists y\, F$ to $\forall x_1 \dots \forall x_n\, F\{y \mapsto f(x_1, \dots, x_n)\}$ for a new function symbol $f$ of arity $n$ (a Skolem function). Structures have nonempty universes, as usual; the rules that move quantifiers are equivalences only under this convention, since over an empty universe $(\exists x\, F) \vee G$ is equivalent to $G$ while $\exists y\,(F\{x \mapsto y\} \vee G)$ is false.

Let $F$ be a closed formula over a signature $\Sigma$, let $F \Rightarrow_P^* G$ with $G$ in prenex form, and let $G \Rightarrow_S^* H$ with $H$ in prenex form without existential quantifiers, over $\Sigma'$, the extension of $\Sigma$ by the Skolem functions. Then

1. $F$ and $G$ are equivalent;
2. $H \models G$, but in general $G \not\models H$;
3. $G$ is satisfiable over $\Sigma$ if and only if $H$ is satisfiable over $\Sigma'$.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.5, prenex normal form, Skolemization and Theorem 3.9, p. 56.
