# Prenex transformation preserves equivalence

A formula is in *prenex form* $Q_1 x_1 \dots Q_n x_n\, G$ if $G$ is quantifier-free and each $Q_i \in \{\forall, \exists\}$. The *prenex transformation* $\Rightarrow_P$ rewrites, at any position of a formula $H$, $F \leftrightarrow G$ to $(F \to G) \wedge (G \to F)$, $\neg Q x\, F$ to $\bar Q x\, \neg F$, $(Q x\, F) \circ G$ to $Q y\,(F\{x \mapsto y\} \circ G)$ for $\circ \in \{\wedge, \vee\}$, $(Q x\, F) \to G$ to $\bar Q y\,(F\{x \mapsto y\} \to G)$, and $F \circ (Q x\, G)$ to $Q y\,(F \circ G\{x \mapsto y\})$ for $\circ \in \{\wedge, \vee, \to\}$, where $y$ is a fresh variable and $\bar Q$ is the quantifier dual to $Q$. Structures have nonempty universes, as usual; the rules that move quantifiers are equivalences only under this convention, since over an empty universe $(\exists x\, F) \vee G$ is equivalent to $G$ while $\exists y\,(F\{x \mapsto y\} \vee G)$ is false.

1. Each $\Rightarrow_P$ step replaces a formula by an equivalent one.
2. $\Rightarrow_P$ terminates, and its normal forms are exactly the formulas in prenex form $Q_1 x_1 \dots Q_n x_n\, G$ with $G$ quantifier-free and without $\leftrightarrow$.

Hence every formula is equivalent to a formula in prenex form, computable by $\Rightarrow_P$.

**Proof sketch.** Each rule is a valid equivalence, the renaming keeping the variable fresh, and equivalence is preserved under replacement in a context. Order formulas lexicographically by the number of biconditionals and then by the sum, over quantifier occurrences, of the number of connectives above each. Removing a biconditional duplicates subformulas but lowers the first component; every other step keeps it and moves one quantifier above one connective, lowering the second. A formula with a biconditional or with a quantifier below a connective admits a step.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.5, prenex normal form (the reduction system $\Rightarrow_P$) and Theorem 3.9 (i), pp. 55–56. The termination argument is written out here.
