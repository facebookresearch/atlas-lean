# Generating function for the total shade of compositions

Let $c(n)$ be the total
shade of the compositions of $n$, and let $q$ be a real number with $0 < q < 1/4$. For natural
numbers $i_2, i_3, s_1, s_3$ put

$$A_{i_2, i_3, s_1, s_3} = (s_1 - s_3) \prod_{i_3 < i < i_2} (1 - q^{s_1 - i + 1}) +
\sum_{i_3 < j < i_2} \Big( \prod_{i_3 < i < i_2, i \ne j} (1 - q^{s_1 - i + 1}) \Big)
\frac{j(q - 1) + q^{s_1 + 1 - j} + s_1 - q(1 + s_1)}{1 - q},$$



$$B_{i_2} = 1 + \sum_{m \ge 1} q^{-i_2 m - m(m - 1)/2} (1 - q)^{-m} q^{m(1 + 2 i_2 + m)/2},$$

and for natural numbers $i, j, s$ put

$$E_{i, j, s} = -1 - q^{1 - i - j + s} (-2 + i + j - s) + q^{2 - i - j + s} (-1 + i + j - s).$$

Let

$$D_L(q) = \sum_{i_1 \ge 1} \sum_{s_1 \ge i_1 + 2} \Big( \frac{1}{1 - q} \Big)^{i_1 - 2}
\Big( \prod_{r=1}^{i_1 - 1} (1 - q^{s_1 - r}) \Big) q^{i_1 (i_1 - 1)/2 - i_1 s_1}
\sum_{i_2 = i_1 + 2}^{s_1 + 1} \sum_{s_2 \ge s_1 + 1} \sum_{i_3 = i_1 + 1}^{i_2 - 1}
\sum_{s_3 = i_3}^{s_1 - 1} q^{i_3 s_1 + s_2 + s_3 - (i_3 + i_3^2)/2}
\Big( \frac{1}{1 - q} \Big)^{i_2 - i_3} A_{i_2, i_3, s_1, s_3} B_{i_2},$$



$$D_R(q) = \sum_{i \ge 1} \sum_{s \ge i} \Big( \prod_{r=1}^{i-1} (1 - q^{s - r}) \Big)
\frac{q^s}{(1 - q)^{i-1}} \Big( \binom{s - i + 1}{2} \sum_{m=0}^{s-1} \frac{q^m}{(1 - q)^m}
\prod_{r=1}^{m} (1 - q^{s + 1 - i - r}) +
\frac{1}{(1 - q)^2} \sum_{m=1}^{s-1} \sum_{j=1}^{m} \frac{q^m}{(1 - q)^{m-1}}
\Big( \prod_{1 \le r \le m, r \ne j} (1 - q^{s + 1 - i - r}) \Big) E_{i, j, s} \Big).$$

Then

$$\sum_{n \ge 0} c(n) q^n = D_L(q) + D_R(q).$$

Empty sums are $0$ and empty products are $1$; all exponents are integers and may be
negative. For $0 < q < 1/4$ all these series converge absolutely.

This is Theorem 1 of the paper with two corrected readings. In the paper's display for
$D_L(q)$ the outer double sum over $i_1, s_1$ (and the left-hand side $L(x, q, u)$) is
duplicated, a typesetting slip; reading it once reproduces the printed expansion
$2q^6 + 6q^7 + 24q^8 + \cdots$. In the display for $D_R(q)$ the product in the double sum
over $m, j$ runs over $r \ne j$, as in the paper's display (R) from which it is obtained by
setting $x = 1$; with the product over all $r$ as printed, the coefficient of $q^4$ in
$D_R(q)$ is $14$ instead of the printed $13$, and $D_L + D_R$ no longer matches the total
shade.

## Sources

- Aubrey Blecher, Arnold Knopfmacher and Michael Mays, *Shade in Compositions of Integers*, Journal of Integer Sequences 27 (2024), Article 24.5.6, Theorem 1 (`jis-2024-24.5.6-thm-1`).
