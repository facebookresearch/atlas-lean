# Rotation orbits correspond to conjugate elements

Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then for all
$a, b \in F^n$, the tuple $b$ lies in the rotation orbit of $a$ if and only if $\Phi(a)$ and
$\Phi(b)$ have the same minimal polynomial over $F$.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 29 (`jis-2026-26.4.6-cor-29`).
