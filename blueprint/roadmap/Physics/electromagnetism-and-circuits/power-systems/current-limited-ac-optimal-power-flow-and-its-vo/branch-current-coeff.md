# Coefficient matrix of the squared current on a branch

For natural numbers $n$ and $m$, a real matrix $B \in \mathbb{R}^{n \times m}$, branch admittances
$y \in \mathbb{C}^m$ and a branch $e$, the branch-current coefficient matrix is the complex
$n \times n$ matrix with entries

$$(C_e)_{ab} = |y_e|^2\, B_{ae}\, B_{be},$$

that is $C_e = |y_e|^2\, b_e b_e^{\mathsf T}$ with $b_e$ the column $e$ of $B$. Its entries are real
and it is [Hermitian](branch-current-coeff-is-hermitian.md). On the [voltage lift](voltage-lift.md)
of $V$ its [pairing](pairing.md) is the
[squared branch current](pairing-branch-current-coeff-voltage-lif.md) $|y_e (B^{\mathsf T} V)_e|^2$.
