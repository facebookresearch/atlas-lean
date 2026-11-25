# The quotient of a key-equation solution is the message

Let $F$ be a field, let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct and let $k, e$ be natural numbers
with $2e + k \le n$. Let $p \in F[X]$ have degree less than $k$, and let $y \in F^n$ be
within Hamming distance $e$ of $(p(\alpha_0), \dots, p(\alpha_{n-1}))$. If $(Q, E)$ solves
the key equations for $y$ ($E$ is monic of degree $e$, $\deg Q < e + k$, and
$Q(\alpha_i) = y_i E(\alpha_i)$ for all $i < n$), then the quotient of $Q$ by $E$ is $p$.
