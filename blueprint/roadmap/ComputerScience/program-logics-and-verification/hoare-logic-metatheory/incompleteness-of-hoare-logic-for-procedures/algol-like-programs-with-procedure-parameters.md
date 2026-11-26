# Algol-like programs with procedure parameters

Fix a first-order expression language $L_E$, an assertion language $L_A$ and an interpretation $I$ of both. Clarke's statements are built from assignments $x := t$, conditionals, $\mathbf{while}$ loops, blocks $\mathbf{begin}\ B_1; \dots; B_k\ \mathbf{end}$ that may declare local variables ($\mathbf{new}\ x$) and procedures, and calls $\mathbf{call}\ q(\bar a : \bar P)$. A procedure declaration $\mathbf{proc}\ q(\bar x : \bar p); K\ \mathbf{end}$ has variable parameters $\bar x$ and procedure parameters $\bar p$. The meaning $M[S](e, s)$ of a statement $S$ in an environment $e$ (the procedure declarations in force) and a state $s$ is the final state, or undefined if $S$ diverges. Block entry renames local identifiers, which makes scope *static*: a call is elaborated in the environment of the procedure's declaration, not of the call. The features in question are (i) procedures as parameters of calls, (ii) recursion, (iii) static scope, (iv) global variables and (v) internal procedures, that is, procedures declared inside procedures.

A partial-correctness assertion $\{P\}\, S\, \{Q\}/e$ with $P, Q \in L_A$ is *true* in $I$ if $M[S](e, s) = s'$ and $s \in P$ imply $s' \in Q$, and every procedure global to $S$ or to a procedure declaration in $e$ is declared in $e$. $L_A$ is *expressive* with respect to $L_E$ and $I$ if for all $S$, $e$ and $Q$ some formula of $L_A$ defines the weakest precondition $\mathrm{WP}(S, e, Q) = \{s : M[S](e, s) \text{ is undefined or lies in } Q\}$. A Hoare axiom system $H$ for a programming language is *sound and complete in the sense of Cook* if, for every $L_A$, $L_E$, $I$ and proof system $T$ for $L_A$ such that $L_A$ is expressive with respect to $L_E$ and $I$ and $T$ proves exactly the formulas of $L_A$ true in $I$, an assertion is derivable in $H$ from $T$ if and only if it is true in $I$.

## Related topics

- [Cook's relative completeness theorem for Hoare logic](../../hoare-logic/cook-s-relative-completeness-theorem-for-hoare.md)

## Sources

- E. M. Clarke, "Programming language constructs for which it is impossible to obtain good Hoare axiom systems", *Journal of the ACM* 26(1):129–147, 1979, <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/emc/www/papers/Papers%20In%20Refereed%20Journals/79_impossible_hoareaxiom.pdf>, Section 2, Definitions 2.1–2.3.
