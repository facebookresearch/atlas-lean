# Finite validity check for a frame condition

Given a condition $C$ on pairs $(U, R)$ of a
finite set $U$ of sets of formulas and a finite set $R$ of pairs of such sets, a formula $\varphi$
passes the finite check for $C$ when, for every nonempty set $U$ of subsets of the subformulas of
$\varphi$ and every relation $R \subseteq U \times U$ with $C(U, R)$, $\varphi$ holds at every
$s \in U$ in the Kripke model with worlds $U$, accessibility relation $R$, and an atom true at
$s$ iff it belongs to $s$.
