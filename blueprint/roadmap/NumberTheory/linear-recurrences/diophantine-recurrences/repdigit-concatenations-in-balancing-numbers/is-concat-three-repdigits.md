# Concatenations of three decimal repdigits

A natural number $n$ is a concatenation of
three repdigits if there are digits $d_1, d_2, d_3$ with $1 \le d_1 \le 9$, $0 \le d_2 \le 9$,
$0 \le d_3 \le 9$, $d_1 \ne d_2$ and $d_2 \ne d_3$, and block lengths $m_1, m_2, m_3 \ge 1$, such
that the decimal expansion of $n$ is $m_1$ copies of $d_1$, then $m_2$ copies of $d_2$, then $m_3$
copies of $d_3$; that is,

$$9n = d_1 (10^{m_1} - 1) 10^{m_2 + m_3} + d_2 (10^{m_2} - 1) 10^{m_3} + d_3 (10^{m_3} - 1).$$

Equivalently, the decimal expansion of $n$ has exactly three runs of equal digits.

## Sources

- Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 4 and 6.
