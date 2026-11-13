# Safety formulas as LTL formulas

The translation $t$ of safety formulas into LTL formulas
is defined by recursion: $t(\varphi)$ is the LTL translation of $\varphi$ for a propositional
formula $\varphi$; $t(\psi \wedge \rho) = t(\psi) \wedge t(\rho)$;
$t(\psi \vee \rho) = \neg(\neg t(\psi) \wedge \neg t(\rho))$, the derived LTL disjunction;
$t(X\,\psi) = X\,t(\psi)$, where $X$ is next; and $t(G\,\varphi) = G\,t(\varphi)$ for a
propositional formula $\varphi$, where $G$ is the derived LTL operator always.
