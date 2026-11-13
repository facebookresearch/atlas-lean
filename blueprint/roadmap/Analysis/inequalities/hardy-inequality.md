# Hardy's inequality

Let $p > 1$ be a real number and let $(a_n)_{n \ge 0}$ be a sequence
of nonnegative real numbers such that $\sum_n a_n^p$ converges. Write
$A_n = \frac{1}{n+1} \sum_{i=0}^{n} a_i$ for the average of $a_0, \dots, a_n$. Then
$\sum_n A_n^p$ converges and

$$\sum_{n=0}^{\infty} A_n^p \le \left(\frac{p}{p-1}\right)^p \sum_{n=0}^{\infty} a_n^p.$$

Proof: Elliott's finite telescoping argument is combined with Young's and Hölder's inequalities,
following E. B. Elliott (1926) as presented in Hardy--Littlewood--Pólya, *Inequalities*,
Theorem 326.

## Sources

- G. H. Hardy, *Note on a theorem of Hilbert*, Mathematische Zeitschrift 6 (1920), 314-317: the discrete series form with constant `(p / (p - 1)) ^ p` for `p > 1`.
