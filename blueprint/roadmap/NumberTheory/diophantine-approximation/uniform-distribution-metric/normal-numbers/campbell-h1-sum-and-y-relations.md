# Sums of $h_1$ and the jumps of $h_2$ at powers of ten

Let $h_1$ be Campbell's auxiliary
sequence and $h_2$ Campbell's sequence. For every integer $\ell \ge 1$,
$\sum_{i=1}^{10^{\ell+1}-1} h_1(i) = \sum_{j=0}^{\ell-1} 900 \cdot 100^j$, the number written
$9090\cdots900$ ($\ell$ blocks $90$, then $0$). Moreover, writing $y_1(n) = h_2(10^{n-1})$ and
$y_2(n) = h_2(10^n - 1)$, for every integer $\ell \ge 2$ we have
$(y_2(\ell) - y_1(\ell)) / (9 \cdot 10^{\ell-1} - 1) = 10^{\ell-1}$ and
$y_1(\ell + 1) - y_2(\ell) = 10^{2\lfloor \ell/2 \rfloor}$.

## Sources

- John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 2 (`jis-2026-26.3.4-lem-2`).
