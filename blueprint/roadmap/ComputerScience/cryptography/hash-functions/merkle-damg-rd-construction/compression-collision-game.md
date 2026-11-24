# Compression-function collision game

Let $h : S \times B \to S$ be a compression function
and let $A$ be an adversary that maps random coins $r$ from a finite nonempty type $R$ either to a
pair $(p_1, p_2)$ of compression inputs in $S \times B$ or to no output. The game is the
distribution of the Boolean outcome when $r$ is drawn uniformly from $R$: the adversary wins
(outcome true) exactly when $A(r)$ is a pair $(p_1, p_2)$ with $p_1 \ne p_2$ and
$h(p_1) = h(p_2)$, and loses when $A(r)$ is no output.
