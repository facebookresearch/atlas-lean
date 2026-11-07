# Rectangular peg theorem (Greene–Lobb)

Let $\gamma : S^1 \to \mathbb{C}$ be a $C^\infty$
embedding of the unit circle (a smooth Jordan curve in the plane). For $z, w \in \mathbb{C}$ and
an angle $\theta$, write $R(z, w, \theta)$ for the list of the four points $z e^{i\theta}$,
$(\operatorname{Re} w + i \operatorname{Im} z) e^{i\theta}$, $w e^{i\theta}$,
$(\operatorname{Re} z + i \operatorname{Im} w) e^{i\theta}$, in this order: the vertices of the
(possibly degenerate) axis-parallel rectangle with opposite corners $z$ and $w$, rotated about
the origin by $\theta$. Then for all $z$, $w$, $\theta$ there exist $z'$, $w'$, $\theta'$ such
that $R(z, w, \theta)$ is similar to $R(z', w', \theta')$, meaning that for some real $r > 0$
the distance between the $i$-th and $j$-th vertices of $R(z, w, \theta)$ is $r$ times the
distance between the $i$-th and $j$-th vertices of $R(z', w', \theta')$ for all $i, j$, and all
four vertices of $R(z', w', \theta')$ lie on $\gamma$.

## Sources

- J. E. Greene and A. Lobb, `The rectangular peg problem`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-RectangularPegProblem.lean Via leanprover/lean-eval@38361be, problem `annals_rectangular_peg_problem`.
