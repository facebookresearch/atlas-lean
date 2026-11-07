# Some generalized Euclid sequence contains every prime

Let $P$ be a finite set of primes
and let $k$ be the number of elements of $P$. Then there is an injective sequence
$a_0, a_1, a_2, \dots$ of primes such that $a_0, \dots, a_{k-1}$ are exactly the elements of $P$,
every prime occurs in the sequence, and for every $n \ge k$ there is a set
$I \subseteq \{0, \dots, n-1\}$ such that $a_n$ divides

$$\prod_{i \in I} a_i + \prod_{i \in \{0, \dots, n-1\} \setminus I} a_i.$$

This is an existence claim over all choices of $I$ and of the prime divisor, unlike the open
Euclid–Mullin conjecture about one specific sequence. For distinct primes $p_1, \dots, p_r$ and
any $J \subseteq \{1, \dots, r\}$, the number
$\prod_{i \in J} p_i + \prod_{i \in \{1, \dots, r\} \setminus J} p_i$ is coprime to
$p_1 \cdots p_r$, so a prime divisor of it is always new.

Proof: Booker's residue-set route, with an elementary squarefree count in place of Rogers'
density bound and Jacobi-sum character-sum bounds in place of the Hasse and Weil bounds.

## Sources

- Andrew R. Booker, "A Variant of the Euclid-Mullin Sequence Containing Every Prime," Journal of Integer Sequences 19 (2016), Article 16.6.4, Theorem, lines 132–136, https://cs.uwaterloo.ca/journals/JIS/VOL19/Booker/book3.tex
