# The $p$-dissection of $f_1$

Let $p \ge 5$ be a prime, let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for $k \ge 1$, and let
$f(a, b) = \sum_{m \in \mathbb{Z}} a^{m(m+1)/2} b^{m(m-1)/2}$ be Ramanujan's general theta
function. Put $c = (p-1)/6$ if $p \equiv 1 \pmod 6$ and $c = (-p-1)/6$ otherwise. Then, as
integer power series,

$$
f_1 = \sum_{t=-(p-1)/2,\ t \ne c}^{(p-1)/2} (-1)^t q^{(3t^2+t)/2}
f\bigl(-q^{(3p^2+(6t+1)p)/2}, -q^{(3p^2-(6t+1)p)/2}\bigr) +
(-1)^c q^{(p^2-1)/24} f_{p^2}.
$$

Moreover, $(3t^2 + t)/2 \not\equiv (p^2 - 1)/24 \pmod p$ for every integer $t$ with
$-(p-1)/2 \le t \le (p-1)/2$ and $t \ne c$.

## Sources

- Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock Theta Functions*, INTEGERS 25 (2025), Article A72, Lemma 2.
