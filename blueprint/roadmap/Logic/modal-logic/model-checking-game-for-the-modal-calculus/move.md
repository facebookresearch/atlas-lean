# Moves of the μ-calculus model-checking game

Fix a Kripke model $M$ with accessibility
relation $R$. A game position $(\varphi, w, s)$ consists of a μ-calculus formula $\varphi$ (with
de Bruijn variables), a world $w$ and a stack $s$ of fixpoint binders, innermost first. The
moves are exactly the following. From $(\varphi \wedge \psi, w, s)$ and from
$(\varphi \vee \psi, w, s)$ to $(\varphi, w, s)$ and to $(\psi, w, s)$. From
$(\Box \varphi, w, s)$ and from $(\Diamond \varphi, w, s)$ to $(\varphi, v, s)$ for every world
$v$ with $w R v$. From $(\mu \varphi, w, s)$ to $(\varphi, w, s')$, where $s'$ is $s$ with
$\mu \varphi$ pushed on top, and likewise from $(\nu \varphi, w, s)$ to $(\varphi, w, s'')$,
where $s''$ is $s$ with $\nu \varphi$ pushed on top. From $(x_n, w, s)$, where $x_n$ is the
variable with de Bruijn index $n$ and $n$ is less than the length of $s$, to $(s_n, w, t)$,
where $s_n$ is the entry of $s$ at index $n$ (counting from $0$) and $t$ is $s$ with its first
$n + 1$ entries removed.

## Sources

- C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6.
