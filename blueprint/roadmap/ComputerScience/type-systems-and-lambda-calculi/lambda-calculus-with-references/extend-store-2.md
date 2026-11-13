# Retyping a well-typed store under an extended store typing

Let $\Gamma$ be a variable
context, let $S$ and $S'$ be store typings such that $S$ is a prefix of $S'$, and let $\mu$ be a
store that is well typed under $\Gamma$ and $S$. Then $\mu$ and $S$ have the same length, and for
every location $l$ less than this length, the entry of $\mu$ at $l$ is a value that has, under
$\Gamma$ and $S'$, the type that $S$ assigns to $l$.
