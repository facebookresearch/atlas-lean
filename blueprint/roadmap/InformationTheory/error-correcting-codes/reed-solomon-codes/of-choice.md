# A key-equation solver by choice

For points $\alpha_0, \dots, \alpha_{n-1}$ in a field
$F$ and natural numbers $k$ and $e$, this is the solver for the key equations that, on a received
word $y \in F^n$, returns a pair $(Q, E)$ of polynomials solving the key equations for $y$ (that
is, $E$ is monic of degree $e$, $\deg Q < e + k$ and $Q(\alpha_i) = y_i E(\alpha_i)$ for all $i$),
picked by the axiom of choice, whenever such a pair exists, and reports failure otherwise.
