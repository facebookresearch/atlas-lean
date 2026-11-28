# Disjunction of a list of formulas

The disjunction of a finite list of [observation formulas](observation-formula.md) is defined by right folding: the empty list gives $\bot = \neg\top$, and the list $\varphi :: \Phi$ gives $\varphi \vee \bigvee\Phi$, where $\psi \vee \chi = \neg(\neg\psi \wedge \neg\chi)$. In particular the disjunction of the one-element list $[\varphi]$ is the formula $\varphi \vee \bot$, not $\varphi$ itself.
