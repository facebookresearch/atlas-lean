# Sloane's endpoint formula for reverse multiples

Let $g$ and $k$ be integers with
$2 \le k < g$, and let $N = (a_n a_{n-1} \cdots a_0)_g$ have base-$g$ digits
$a_0, \dots, a_n \in \{0, \dots, g - 1\}$, with units digit $a_0$ and leading digit $a_n \ne 0$.
Suppose $N$ is a $(g, k)$ reverse multiple, that is, $k N = (a_0 a_1 \cdots a_n)_g$, and that
$a_0 + a_n = g$. Then $(k + 1) a_n = g$; in particular $k + 1$ divides $g$ and
$a_n = g / (k + 1)$.

## Sources

- L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer Sequences 18 (2015), Article 15.9.7, Corollary `cor:lastdig1089` (Sloane's Conjecture 3.5) and proof, lines 418–424, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>. Proves `Wanted` entry `sloane_reverse_multiple_endpoint`.
