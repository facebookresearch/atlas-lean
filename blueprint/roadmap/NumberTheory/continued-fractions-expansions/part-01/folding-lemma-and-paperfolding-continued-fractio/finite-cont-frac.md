# Value of a finite continued fraction

For a finite list $a_0, a_1, \dots, a_t$ of integers
(possibly zero or negative), the value $[a_0; a_1, \dots, a_t]$ is the rational number
$a_0 + 1/(a_1 + 1/(\cdots + 1/a_t))$, computed from the right: the empty list has value $0$, and
the list $a_0, a_1, \dots, a_t$ has value $a_0 + v^{-1}$, where $v$ is the value of the list
$a_1, \dots, a_t$. In particular $[a] = a + 0^{-1} = a$; here and at any vanishing intermediate
denominator, $0^{-1}$ is taken to be $0$.

## Sources

- Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation).
