# Realization is stable under renaming

Fix an interpretation $I$ of the base types. Let
$v$ be a Kripke semantic value of type $A$ in context $\Gamma$ that realizes an element $d$ of
the denotation of $A$ at an environment $\eta$ for $\Gamma$. If $\rho : \Gamma \to \Delta$ is a
renaming and $\theta$ is an environment for $\Delta$ with $\theta \circ \rho = \eta$, then the
transport of $v$ along $\rho$ realizes $d$ at $\theta$.
