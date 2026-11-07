# Mean number of short chords in linear $k$-chord diagrams

Let $k \ge 1$ and $n \ge 0$ be
integers. A linear $k$-chord diagram of length $kn$ is a set of $n$ subsets of
$\{0, 1, \dots, kn - 1\}$, each with $k$ elements, whose union is $\{0, 1, \dots, kn - 1\}$; it
is therefore a partition of this set into $n$ blocks of size $k$, its chords. A chord is short
when it consists of $k$ consecutive integers $\{i, i + 1, \dots, i + k - 1\}$. The number of
short chords, averaged over all linear $k$-chord diagrams of length $kn$, equals

$$
\frac{n\,(kn - k + 1)}{\binom{kn}{k}},
$$

where for $n = 0$ the denominator $\binom{0}{k}$ is $0$ and the quotient is read as $0$, which
is the mean over the single empty diagram.

For $n \ge 1$ there are $kn - k + 1$ sets of $k$ consecutive integers in $\{0, \dots, kn - 1\}$.
This is the mean theorem, distinct from the same paper's asymptotic Poisson distribution of
short chords.

## Sources

- Donovan Young, "Linear k-Chord Diagrams," Journal of Integer Sequences 23 (2020), Article 20.9.1, Theorem, lines 208–214, https://cs.uwaterloo.ca/journals/JIS/VOL23/Young/young5.tex
