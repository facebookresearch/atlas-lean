# $2$-adic dissection of the Gamma quadratic ratio

Let $a, b, z$ be complex numbers such
that $m^2 + 2am + b \ne 0$ and $m^2 + 2am + b - z \ne 0$ for every integer $m$ that is nonnegative
or of the form $m = -2^j$ with $j \ge 0$ an integer. For $j \ge 0$ put $a_j = a / 2^{j+1} - 1/2$
and $b_j = 1/4 - a / 2^{j+1} + b / 2^{2j+2}$. Then the Gamma quadratic ratio $g$ satisfies
$g(a, b, z) = \prod_{j \ge 0} g(a_j, b_j, z / 2^{2j+2})$.

The source prints the parameters $a / 2^j - 1$ and $1 - a / 2^{j+1} + b / 2^{2j+2}$, which make
the identity false: for $a = 3/10$, $b = -2$, $z = 7/10$ the left side is about $1.6283$ and the
printed product about $6.18 \cdot 10^4$, while the product above matches. The parameters $a_j$,
$b_j$ come from the penultimate line of the source's proof, which writes
$m^2 + 2am + b = 2^{2j+2}(n^2 + 2 a_j n + b_j)$ for $m = (2n - 1) 2^j$. The hypotheses, absent
from the source, exclude the poles of every Gamma factor on both sides and the vanishing of $b$
and $b - z$.

## Sources

- Christophe Vignat and Michael Milgram, *Curious Multisection Identities by Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 23 (`jis-2024-24.5.5-prop-23`).
