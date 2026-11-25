# RSA inverter from a factoring algorithm

From a factoring algorithm $F$, the RSA inverter on a public key $(n, e)$, a value $y \in \mathbb{Z}/n$
and coins $s$ factors $n$ as $(a, b) = F(n, s)$, takes $d'$ to be the representative in
$\{0, \dots, \varphi - 1\}$ of the inverse of $e$ modulo $\varphi = (a - 1)(b - 1)$, and outputs
$y^{d'}$ (Katz and Lindell, Section 8.2.4: if factoring is easy, then so is RSA). Here $a - 1$ is taken
to be $0$ when $a = 0$, and likewise for $b$; when $\varphi = 0$ or $e$ is not invertible modulo
$\varphi$, $d'$ is a conventional value instead.
