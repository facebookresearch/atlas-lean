# Ridout's $p$-adic extension of Roth's theorem

Let $\xi$ be an irrational real algebraic
number, let $\varepsilon > 0$, and let $S$ be a finite set of primes. For a rational number $r$,
write $r = p/q$ in lowest terms with $p \in \mathbb{Z}$ and $q \ge 1$, and let
$H(r) = \max(|p|, q)$ be its height. For a prime $\ell$, let $|\cdot|_\ell$ be the $\ell$-adic
absolute value on $\mathbb{Q}$, normalized by $|\ell|_\ell = \ell^{-1}$. Then only finitely many
rationals $r = p/q$ satisfy

$$\Bigl(\prod_{\ell \in S} |p|_\ell |q|_\ell\Bigr) |\xi - r| < \frac{1}{H(r)^{2 + \varepsilon}}.$$

The source prints the right side as $1/q^{2 + \varepsilon}$. Over all rationals that bound fails:
with $2 \in S$ and $\xi = \sqrt{2}$, every $r = 2^k$ with $k \ge 1$ gives left side
$1 - \sqrt{2}/2^k < 1$, so the height $H(r)$ is used instead.

Proof: The proof follows Roth's auxiliary-polynomial and index route, with the
S-adic integrality step supplied by valuation divisibility and a finite pigeonhole.

## Sources

- Boris Adamczewski, "The Many Faces of the Kempner Number", Journal of Integer Sequences 16 (2013), Article 13.2.15, `thmRi` environment, lines 736–746, attributed there to Ridout, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Adamczewski/adam6.tex>.
