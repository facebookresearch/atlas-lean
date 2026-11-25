# Euler polynomials at $(x + 1)/2$ as an Appell sequence

Over $\mathbb{Q}$, let $S(z) = 2e^z / (1 + e^{2z})$ and $\Delta = e^z - 1$ as formal power series, let
$E_n(x)$ be the Euler polynomials, and let $\alpha_k$ be the coefficients with $\alpha_0 = 1$,
$\alpha_1 = 0$, $\alpha_{k+2} = -\alpha_{k+1} - \alpha_k/2$. Then

1. $2^n E_n\bigl((x + 1)/2\bigr) = S(D)(x^n)$ for every $n \ge 0$, where $S(D)$ is the composition
   operator of $S$ and $D$ is differentiation;
2. $S \cdot (2 + 2\Delta + \Delta^2) = 2 + 2\Delta$; and
3. $S = \sum_{k \ge 0} \alpha_k \Delta^k$, the series $\sum_k \alpha_k z^k$ with $\Delta$ substituted for $z$.

The source prints the denominator of $S$ as $2 + e^{2z}$, which contradicts its own expressions
$e^z S_E(2z)$ and $(2 + 2\Delta)/(2 + 2\Delta + \Delta^2)$; this statement uses $1 + e^{2z}$.

## Sources

- Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif, "Generalizations of Several Explicit Formulas for Euler Polynomials", INTEGERS 25 (2025), Article A65, Lemma 2.3.
