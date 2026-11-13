# Digit sums of the words between markers

Let $F_n$ be the Fibonacci numbers, with
$F_0 = 0$ and $F_1 = 1$. For every $j$ (words counted from zero), the digit sum of the $j$-th
word between markers of the unsum gap sequence, plus $2$, equals $F_{\lfloor j/2 \rfloor + 5}$.

So the digit sums are $3, 3, 6, 6, 11, \ldots$; adding the preceding marker digit $2$ gives
$F_5, F_5, F_6, F_6, F_7, \ldots$, which is how the source's Lemma 3 must be read, since the
bare digit sum of the first word is $3 \ne F_5 = 5$.

## Sources

- Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8, Lemma 3 (`jis-2025-25.3.8-lem-3`).
