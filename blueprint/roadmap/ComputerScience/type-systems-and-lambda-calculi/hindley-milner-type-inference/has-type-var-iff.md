# Typing inversion for variables

Let $\Gamma$ be a typing context, $x$ a name and $\tau$ a
monotype. Then $\Gamma \vdash x : \tau$ holds for the variable expression $x$ if and only if
there are a type scheme $\sigma$ and monotypes $(t_i)_{i \in \mathbb{N}}$ such that the lookup of
$x$ in $\Gamma$ gives $\sigma$ and $\tau$ is the instance of $\sigma$ at $(t_i)$.
