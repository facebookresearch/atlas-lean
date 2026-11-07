# Mex step for chocolate bars with many functions

Let $m$ be a natural number, let
$f_1, \dots, f_m : \mathbb{N} \to \mathbb{N}$ have the NS property, and let
$x_1, \dots, x_m, z, c$ be natural numbers with $x_t \le f_t(z)$ for all $t$ and
$c < x_1 \oplus \cdots \oplus x_m \oplus z$, where $\oplus$ is nim-sum (bitwise exclusive or).
Then either there are an index $i$ and some $u < x_i$ such that $c$ is the nim-sum
$x_1 \oplus \cdots \oplus x_m \oplus z$ with $x_i$ replaced by $u$, or there is some $w < z$
with $c = \min(x_1, f_1(w)) \oplus \cdots \oplus \min(x_m, f_m(w)) \oplus w$.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Lemma 4 (`integers-2025-G3-lem-4`).
