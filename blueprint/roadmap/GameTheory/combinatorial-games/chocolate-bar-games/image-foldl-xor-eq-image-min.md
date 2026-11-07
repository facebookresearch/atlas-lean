# Nim-sum sets under clamping by functions with the NS property

Let $m \in \mathbb{N}$,
let $f_0, \dots, f_{m-1} : \mathbb{N} \to \mathbb{N}$ have the NS property, and let
$x_0, \dots, x_{m-1}, z \in \mathbb{N}$ satisfy $x_t \le f_t(z)$ for every $t < m$. Then

$$
\{x_0 \oplus \cdots \oplus x_{m-1} \oplus w : w < z\} =
\{\min(x_0, f_0(w)) \oplus \cdots \oplus \min(x_{m-1}, f_{m-1}(w)) \oplus w : w < z\},
$$

where $\oplus$ denotes nim-sum (bitwise exclusive or).

The printed left-hand nim-sum carries a stray index $j \ne i$ with $i$ unbound; it is read as the
full nim-sum, as in Lemma 5 (the case of two functions), which the proof generalises.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Lemma 6 (`integers-2025-G3-lem-6`).
