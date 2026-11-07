# The partition function $c_8$

For $n \ge 0$, $c_8(n)$ is the number of partitions of $n$
such that either (a) all parts are even and distinct, or (b) for some positive integer $j$, the
largest odd part is $2j - 1$, every positive odd integer $i \le j$ appears once or twice, every
odd integer $i$ with $j < i \le 2j - 1$ appears exactly once, all even parts are distinct, and
every even part greater than $j$ is at least $2j + 2$.

For $j = 1$ the paper's clauses "the largest odd part $2j - 1$ appears once" and "odd integers
$\le j$ appear once or twice" conflict; the second governs, as in the generating function
$(q^2;q^2)_\infty \sum_n q^{n^2}/(q;q)_n$ the paper uses (the other reading gives $c_8(2) = 1$,
contradicting Theorem 11 of the paper since $31$ is not a square).

## Sources

- John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Section 3 (definition of `c₈`, from Nyirenda and Mugwangwavari).
