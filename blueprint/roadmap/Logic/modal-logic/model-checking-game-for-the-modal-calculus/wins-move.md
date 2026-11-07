# Wins-guided move

Let $M$ be a Kripke model, and identify each fixpoint-free formula with
its embedding into the μ-calculus. For a μ-calculus formula $\psi$, a world $w$ and a stack $s$
of fixpoint binders, the Wins-guided move at the game position $(\psi, w, s)$ is the following
position. If $s$ is empty and $\psi$ is a fixpoint-free disjunction $\psi_1 \lor \psi_2$, it is
$(\psi_1, w, [])$ when $\psi_1$ is winning at $w$ (in the backward-induction winning region of
the fixpoint-free fragment) and $(\psi_2, w, [])$ otherwise. If $s$ is empty and $\psi$ is a
fixpoint-free formula $\Diamond \psi_1$, it is $(\psi_1, v, [])$ for a chosen successor $v$ of
$w$ at which $\psi_1$ is winning, if one exists; otherwise $(\psi_1, v, [])$ for a chosen
successor $v$ of $w$, if one exists; otherwise $(\psi, w, [])$. In every other case: at a
disjunction $\varphi_1 \lor \varphi_2$ it is $(\varphi_1, w, s)$; at $\Diamond \varphi_1$ it is
$(\varphi_1, v, s)$ for a chosen successor $v$ of $w$ if one exists, and $(\psi, w, s)$
otherwise; at $\nu \varphi_1$ it is $(\varphi_1, w, s')$, where $s'$ is $s$ with
$\nu \varphi_1$ pushed on top; and at every remaining formula (the positions owned by Refuter)
it is $(\psi, w, s)$.

Only the left disjunct is tested: if a fixpoint-free disjunction is winning at $w$ and its left
disjunct is not, then its right disjunct is.

## Sources

- C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6.
