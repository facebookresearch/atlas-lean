# Sendov's solution of Blumenthal's minimax angle problem (Erdős Problem 504)

For a natural
number $N$, let $\alpha_N$ be the minimax angle of $N$ points in the plane: the supremum of the
$\alpha \in [0, \pi]$ such that every set of $N$ points in the plane contains three distinct points
$x, y, z$ with $\angle xyz \ge \alpha$ (the angle at $y$). Then $\alpha_3 = \pi/3$,
$\alpha_4 = \pi/2$, and for all natural numbers $n \ge 2$ and $N$: if $2^n < N \le 2^n + 2^{n-2}$,
then $\alpha_N = \left(1 - \frac{2}{2n + 1}\right)\pi$, and if $2^n + 2^{n-2} < N \le 2^{n+1}$,
then $\alpha_N = \left(1 - \frac{1}{n + 1}\right)\pi$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #504, https://www.erdosproblems.com/504 (status SOLVED); resolution: Bl. Sendov, Minimax of the angles in a plane configuration of points, Acta Math. Hungar. 69 (1995), 27-46, main theorem, as stated in Zbl 0853.52009: α(N) = (1 - 2/(2n+1))π for 2^n < N ≤ 2^n + 2^{n-2} and (1 - 1/(n+1))π for 2^n + 2^{n-2} < N ≤ 2^{n+1}, n ≥ 2; α(3) = π/3, α(4) = π/2, https://doi.org/10.1007/BF01874605.
