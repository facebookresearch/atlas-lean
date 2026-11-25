# Evaluating a symbolic store at an initial state

For a symbolic store $\sigma : \mathbb{N} \to \mathrm{AExp}$ and an IMP state $s : \mathbb{N} \to \mathbb{N}$, the evaluation of $\sigma$ at $s$ is the state $x \mapsto \sigma(x)(s)$, which gives each variable $x$ the value in $s$ of the expression $\sigma(x)$.
