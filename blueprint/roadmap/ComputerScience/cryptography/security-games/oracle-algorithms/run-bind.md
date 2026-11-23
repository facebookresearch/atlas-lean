# Running a sequential composition

Let $c$ be an oracle algorithm with outputs in $\alpha$,
let $g$ map each $a \in \alpha$ to an oracle algorithm with outputs in $\beta$, and let
$O : X \to Y$. Running against $O$ the composition that first runs $c$ and then continues with
$g$ applied to its output gives the output of $g(a)$ run against $O$, where $a$ is the output
of $c$ run against $O$.
