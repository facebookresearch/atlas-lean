# Propositional semantic tableau

Consider propositional formulas over a set $\Pi$ of propositional variables built from $\top$, $\bot$, $\neg$, $\wedge$, $\vee$ and $\to$ (with $\leftrightarrow$ eliminated beforehand), evaluated under valuations $\mathcal A : \Pi \to \{0, 1\}$ in the usual way, $\top$ true and $\bot$ false. Formulas are classified as *conjunctive* ($\alpha$, with components $\alpha_1, \alpha_2$) or *disjunctive* ($\beta$, with components $\beta_1, \beta_2$):

| $\alpha$ | $\alpha_1$ | $\alpha_2$ | $\beta$ | $\beta_1$ | $\beta_2$ |
|---|---|---|---|---|---|
| $F \wedge G$ | $F$ | $G$ | $\neg(F \wedge G)$ | $\neg F$ | $\neg G$ |
| $\neg(F \vee G)$ | $\neg F$ | $\neg G$ | $F \vee G$ | $F$ | $G$ |
| $\neg(F \to G)$ | $F$ | $\neg G$ | $F \to G$ | $\neg F$ | $G$ |

The expansion rules are: *negation elimination* ($\neg\neg F$ yields $F$, $\neg\top$ yields $\bot$, $\neg\bot$ yields $\top$); *$\alpha$-expansion* (append $\alpha_1$ and then $\alpha_2$ below a leaf); and *$\beta$-expansion* (branch the leaf into $\beta_1$ and $\beta_2$). A rule may be applied at a leaf to any formula on the path from the root to that leaf.

A *tableau* for a finite set $\{F_1, \dots, F_n\}$ is a finite tree labelled by formulas: the single path $F_1, \dots, F_n$ is a tableau for the set, and applying an expansion rule to a tableau for the set gives another. An infinite sequence of expansion steps has as its *limit* the union of its stages, a finitely branching tree that may be infinite. A *branch* of a tableau or of a limit tree is a path from the root to a leaf or an infinite path from the root. A branch, in particular a path from the root to a leaf, is *closed* if it contains $\bot$ or both some formula $F$ and $\neg F$, and *open* otherwise; a tableau is closed if all its branches are. A *tableau proof* of $F$ is a closed tableau for $\{\neg F\}$. A branch $\pi$ is *maximal* if every formula on $\pi$ that is not a literal, $\top$ or $\bot$ has been expanded at some node of $\pi$; a tableau is *maximal* if each of its branches is closed or maximal, and *strict* if on each branch the rule for each formula has been applied at most once.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.18, propositional expansion rules and the classification of formulas, p. 95, and tableaux, paths, closedness, maximality and strictness, p. 96.
