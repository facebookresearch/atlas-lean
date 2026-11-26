# Normalization of a flex to Deuring form

Let $W$ be a Weierstrass curve over a field and
$(x_1, y_1)$ a point of $W$ at which $d$ = `W.deuringA₃ x₁ y₁` is nonzero and the flex form
vanishes. Then for every unit $u$ the variable change `W.deuringVariableChange x₁ y₁ u` carries $W$
to the Deuring form $y^2 + (a/u)xy + (d/u^3)y = x^3$, where $a$ is `W.deuringA₁ x₁ y₁`.
