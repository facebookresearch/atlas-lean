# Prenex transformation preserves equivalence

A formula is in *prenex form* $Q_1 x_1 \dots Q_n x_n\, G$ if $G$ is quantifier-free and each $Q_i \in \{\forall, \exists\}$. The *prenex transformation* $\Rightarrow_P$ rewrites, at any position of a formula $H$, $F \leftrightarrow G$ to $(F \to G) \wedge (G \to F)$, $\neg Q x\, F$ to $\bar Q x\, \neg F$, $(Q x\, F) \circ G$ to $Q y\,(F\{x \mapsto y\} \circ G)$ for $\circ \in \{\wedge, \vee\}$, $(Q x\, F) \to G$ to $\bar Q y\,(F\{x \mapsto y\} \to G)$, and $F \circ (Q x\, G)$ to $Q y\,(F \circ G\{x \mapsto y\})$ for $\circ \in \{\wedge, \vee, \to\}$, where $y$ is a fresh variable and $\bar Q$ is the quantifier dual to $Q$. Structures have nonempty universes, as usual; the rules that move quantifiers are equivalences only under this convention, since over an empty universe $(\exists x\, F) \vee G$ is equivalent to $G$ while $\exists y\,(F\{x \mapsto y\} \vee G)$ is false.

If $F$ is a closed formula and $F \Rightarrow_P^* G$ for a formula $G$ in prenex form, then $F$ and $G$ are equivalent.

**Proof sketch.** Each rule is a valid equivalence, the renaming keeping the variable fresh, and equivalence is preserved under replacement in a context, so every step, and hence the whole sequence, replaces a formula by an equivalent one.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.5, prenex normal form (the reduction system $\Rightarrow_P$) and Theorem 3.9 (i), pp. 55–56.
