# Exponential generating function of tournaments with $d$ circular triads

For every natural number $d$, the exponential generating function $G_d(x) = \sum_{n \ge 0} g_d(n)\, x^n/n!$, a formal power series over $\mathbb{Q}$, equals

$$\sum_{p} \frac{r_p!}{\prod_{i} m_i(p)!}\, (1 - x)^{-(1 + r_p)} \prod_{i \in p} A_i(x),$$

the sum over the partitions $p$ of $d$, where $r_p$ is the number of parts of $p$, $m_i(p)$ is the multiplicity of the part $i$ (the product in the denominator over the distinct parts), and the last product runs over the parts of $p$ with multiplicity. Here $g_d(n)$ is the number of tournaments on the labelled players $\{0, \dots, n-1\}$ with exactly $d$ circular triads, a circular triad of a tournament is a set of three players each of whom beats exactly one of the other two; $A_i(x) = \sum_{n} N(n, i)\, x^n/n!$, where $N(n, d)$ is the number of irreducible tournaments on $n \ge 2$ labelled players $\{0, \dots, n-1\}$ with exactly $d$ circular triads (and $0$ for $n \le 1$); a tournament is irreducible when no nonempty proper set of players loses all its games against the complement, and a circular triad of a tournament is a set of three players each of whom beats exactly one of the other two. For $d = 0$ both sides are $1/(1-x)$.

## Sources

- Ian R. Harris and Ryan P. A. McShane, "Counting Tournaments with a Specified Number of Circular Triads", Journal of Integer Sequences 27 (2024), Article 24.8.7, Theorem 10, https://cs.uwaterloo.ca/journals/JIS/VOL27/McShane/mcshane1.html.
