# Injective relabeling preserves derivability

Let $f \colon \alpha \to \beta$ be an
injective map between types of variables. For a formula $\psi$ of a first-order language $L$
with free variables in $\alpha$, write $f(\psi)$ for Mathlib's relabeling of $\psi$ by $f$,
which replaces each free variable $x$ by $f(x)$, and for a finite list $\Gamma$ of such formulas
write $f(\Gamma)$ for the list obtained by applying this to each member of $\Gamma$. If $\Gamma$
is such a list, $\varphi$ is such a formula and $\Gamma \vdash \varphi$ in natural deduction,
then $f(\Gamma) \vdash f(\varphi)$.
