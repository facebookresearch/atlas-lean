# Runge–Kutta stages tend to the vector field as the step shrinks

Let $E$ be a real normed
space, fix an explicit Runge–Kutta method with $s$ stages, a vector field $f$ assigning a vector
$f(t', x) \in E$ to each time $t' \in \mathbb{R}$ and state $x \in E$, a time $t$ and a state
$y \in E$, and suppose that $(t', x) \mapsto f(t', x)$ is continuous at $(t, y)$. For a step
$h \in \mathbb{R}$, let $k_i(h)$ be the $i$-th stage of the method with step $h$. Then for every
natural number $n$ and every stage index $i < n$, $k_i(h) \to f(t, y)$ as $h \to 0$ with
$h \ne 0$.

The proof is by strong induction on the stage index, since earlier stages appear in later ones.
