# Conjunction of a list of formulas

The conjunction of a finite list of [observation formulas](observation-formula.md) is defined by right folding: the empty list gives $\top$, and the list $\varphi :: \Phi$ gives $\varphi \wedge \bigwedge\Phi$. In particular the conjunction of the one-element list $[\varphi]$ is the formula $\varphi \wedge \top$, not $\varphi$ itself.
