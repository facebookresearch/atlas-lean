# Deuring form in level-three coordinates

Under the hypotheses of
`deuringVariableChange_smul`, let $x_2 \ne x_1$ and let $u$ be the unit $d/(x_2 - x_1)$. Then
`W.deuringVariableChange x₁ y₁ u` carries $W$ to $y^2 + \alpha xy + \beta y = x^3$, where $\alpha$
is `W.levelThreeModulus x₁ y₁ x₂` and $\beta$ is `W.levelThreeAbscissa x₁ y₁ x₂`.
