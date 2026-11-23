# Asymptotic count of lunar primes

Fix an integer $b \ge 2$. For $n \ge 1$ let $\pi_b(n)$
be the number of digit strings $(a_0, \dots, a_{n-1})$ with $a_k \in \{0, \dots, b - 1\}$ and
leading digit $a_{n-1} \ne 0$ whose coefficient sequence $(a_0, \dots, a_{n-1}, 0, 0, \dots)$ is a
lunar prime of base $b$; these are the prime lunar numbers of base $b$ with $n$ digits. Then
$\pi_b(n) \sim (b - 1)^2 b^{n-2}$ as $n \to \infty$, as conjectured by Applegate, LeBrun and
Sloane.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Corollary 12 (`jis-2025-25.2.7-cor-12`).
