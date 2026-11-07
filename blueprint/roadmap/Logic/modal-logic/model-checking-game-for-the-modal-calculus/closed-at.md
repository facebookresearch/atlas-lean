# Formulas closed at depth $d$

Closedness of a μ-calculus formula $\varphi$ (with de Bruijn
variables) at a depth $d \in \mathbb{N}$ is defined by recursion on $\varphi$: atoms, negated
atoms, $\bot$ and $\top$ are closed at every depth; the variable with index $n$ is closed at
depth $d$ exactly when $n < d$; $\varphi \wedge \psi$ and $\varphi \vee \psi$ are closed at
depth $d$ when both $\varphi$ and $\psi$ are; $\Box\varphi$ and $\Diamond\varphi$ are closed at
depth $d$ when $\varphi$ is; and $\mu\varphi$ and $\nu\varphi$ are closed at depth $d$ when
$\varphi$ is closed at depth $d + 1$. Thus every free variable of $\varphi$ refers to one of $d$
enclosing binders.

## Sources

- C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6 (de Bruijn variables).
