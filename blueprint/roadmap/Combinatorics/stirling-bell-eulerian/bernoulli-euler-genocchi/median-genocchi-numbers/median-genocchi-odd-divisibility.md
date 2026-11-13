# Divisibility of the median Genocchi numbers

Let $H_{2m+1}$ denote the odd-indexed median
Genocchi values, with the signs given by their defining sum, so that $H_5 = 2$, $H_7 = -8$ and
$H_9 = 56$. For every natural number $n \ge 1$ there is an integer $z$ with $H_{2n+3} = 2^n z$,
and $z \equiv 1 \pmod 6$ if $n$ is odd, while $z \equiv 4 \pmod 6$ if $n$ is even.

Proof: The antisymmetry of the Euler–Seidel matrix of the Genocchi numbers writes $H_{2n+3}$ as
an alternating sum of Legendre–Stirling numbers times $k!\,(k+1)!$. Pulling a power of two out of
each term gives the factor $2^n$; in the remaining sum every term from the fourth on is divisible
by $6$, which gives the residue. The divisibility and residue arguments are Chen's, applied to
this finite sum instead of his continued fraction.

## Sources

- Kwang-Wu Chen, *An Interesting Lemma for Regular C-fractions*, Journal of Integer Sequences 6 (2003), Article 03.4.8: <https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.tex>.
