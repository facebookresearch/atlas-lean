# Multiple harmonic sums

For natural numbers $p$, $r$ and $n$, the multiple harmonic sum
$H_r^{(n)}$ modulo $p$ is the element

$$H_r^{(n)} = \sum_{0 < k_1 < \cdots < k_n \le r} k_1^{-1} \cdots k_n^{-1}$$

of $\mathbb{Z}/p\mathbb{Z}$, where the sum runs over the strictly increasing $n$-tuples of
integers, equivalently over the $n$-element subsets of $\{1, \dots, r\}$, and $k^{-1}$ is the
inverse of $k$ in $\mathbb{Z}/p\mathbb{Z}$ (Mathlib's total inverse, which is the true inverse
whenever $k$ is a unit modulo $p$). In particular $H_r^{(0)} = 1$, and $H_r^{(n)} = 0$ when $n > r$.

## Sources

- Mattarei–Tauraso, "Congruences of Multiple Sums Involving Sequences Invariant Under the Binomial Transform", J. Integer Sequences, <https://cs.uwaterloo.ca/journals/JIS/VOL13/Tauraso/tauraso22.tex>, Lemma.
