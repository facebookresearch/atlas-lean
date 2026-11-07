# Concatenations of two decimal repdigits

A natural number $n$ is a concatenation of two
repdigits if there are digits $d_1, d_2$ with $1 \le d_1 \le 9$, $0 \le d_2 \le 9$ and
$d_1 \ne d_2$, and block lengths $m_1, m_2 \ge 1$, such that the decimal expansion of $n$ is
$m_1$ copies of $d_1$ followed by $m_2$ copies of $d_2$; that is,
$9n = d_1 (10^{m_1} - 1) 10^{m_2} + d_2 (10^{m_2} - 1)$. Equivalently, the decimal expansion of
$n$ has exactly two runs of equal digits.

Because of the condition $d_1 \ne d_2$, a repdigit such as $99$ is not a concatenation of two
repdigits.

## Sources

- Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Lemmas 3 and 5.
