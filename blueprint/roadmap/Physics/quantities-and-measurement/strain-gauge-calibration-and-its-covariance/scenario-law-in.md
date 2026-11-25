# Finite scenario law with every voltage in an interval

For a finite set $\Omega$ of scenarios, real numbers $a$ and $b$, weights
$p : \Omega \to \mathbb{R}$ and scenario voltages $V : \Omega \to \mathbb{R}$, the pair $(p, V)$ is
a scenario law in $[a, b]$ when

$$
p(\omega) \ge 0 \text{ and } a \le V(\omega) \le b \text{ for every } \omega \in \Omega,
\qquad \sum_{\omega \in \Omega} p(\omega) = 1:
$$

$p$ is a probability distribution on the scenarios, and every scenario voltage, including that of a
scenario of weight zero, lies in $[a, b]$. The real masses of a probability mass function qualify as
weights ([real masses form a finite distribution](to-real-weights-is-distribution.md)).