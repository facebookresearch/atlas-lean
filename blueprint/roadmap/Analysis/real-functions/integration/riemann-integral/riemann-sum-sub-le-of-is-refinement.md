# Riemann sums under refinement

Let $f : \mathbb{R} \to \mathbb{R}$, let $T$ and $T'$ be
tagged partitions of $[a, b]$ such that every point of $T$ is a point of $T'$, and let
$\omega \in \mathbb{R}$ satisfy $|f(x) - f(y)| \le \omega$ for all $x, y \in [a, b]$ with
$|x - y| \le \|T\|$, where $\|T\|$ is the mesh of $T$. Writing $S_f(T)$ for the Riemann sum of
$f$ over $T$, we have $|S_f(T) - S_f(T')| \le \omega (b - a)$.

This is Theorem II of the Riemann integral section in oscillation form: an explicit bound
$\omega$ replaces the modulus of continuity, so $f$ need not be continuous.
