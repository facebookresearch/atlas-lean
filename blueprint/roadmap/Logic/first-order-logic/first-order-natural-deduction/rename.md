# Injective renaming preserves derivability

Let $f \colon \alpha \to \beta$ be an
injective map between types of variables. For a formula $\psi$ of a first-order language $L$
with free variables in $\alpha$, write $f(\psi)$ for the renaming of the free variables of
$\psi$ by $f$, and for a finite list $\Gamma$ of such formulas write $f(\Gamma)$ for the list
obtained by renaming each member of $\Gamma$. If $\Gamma$ is such a list, $\varphi$ is such a
formula and $\Gamma \vdash \varphi$ in natural deduction, then $f(\Gamma) \vdash f(\varphi)$.

On formulas this renaming coincides with Mathlib's relabeling of free variables.
