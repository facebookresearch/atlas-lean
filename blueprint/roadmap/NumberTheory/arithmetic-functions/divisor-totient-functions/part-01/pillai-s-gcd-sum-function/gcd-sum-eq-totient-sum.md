# The gcd-sum as a divisor sum of totients

For every positive integer $n$,
$\sum_{j=1}^{n} \gcd(j, n) = n \sum_{d \mid n} \varphi(d)/d$, where $\varphi$ is Euler's totient
function and $d$ runs over the positive divisors of $n$.

Grouping the terms with $\gcd(j, n) = e$, of which there are $\varphi(n/e)$, shows that the sum
equals $\sum_{e \mid n} e \, \varphi(n/e)$.

## Sources

- Kevin A. Broughan, "The Gcd-Sum Function," Journal of Integer Sequences 4 (2001), Article 01.2.2, Theorem 2.3 (equation label 6), lines 220–226, https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex
