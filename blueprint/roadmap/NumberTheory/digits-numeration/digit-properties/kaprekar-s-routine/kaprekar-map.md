# Kaprekar map

For natural numbers $n$ and $\alpha$, take the decimal digits of $\alpha$
(without leading zeros, and no digits at all for $\alpha = 0$) and, if there are fewer than $n$
of them, pad them with leading zeros to a string of exactly $n$ digits. The Kaprekar map sends
$\alpha$ to the Kaprekar difference $\alpha_M - \alpha_L$ of this digit string: the number with
these digits in descending order minus the number with them in ascending order. For
$\alpha < 10^n$ this is the Kaprekar transformation on the set $D_n$ of $n$-digit strings; for
$\alpha \ge 10^n$ nothing is padded and all digits of $\alpha$ are used.

## Sources

- Haruo Iwasaki, *A New Classification of the Kaprekar Numbers*, The Fibonacci Quarterly 62 (2024), Article iwasaki06162024-ASrev2, Definition 1.1.
