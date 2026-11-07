# Schreyer's Fubini formula for r-horse numbers

Let $r \le n$ be natural numbers. For each
$k$, count the surjections $f : \{0, \dots, n - 1\} \to \{0, \dots, k - 1\}$ whose values on the
first $r$ points are strictly increasing, $f(0) < f(1) < \dots < f(r - 1)$, and let $H$ (the
$r$-horse number) be the sum of these counts over $0 \le k \le n$. Then, as rational numbers,

$$
H = \frac{1}{r!} \sum_{j=0}^{r} (-1)^j \, c(r, r - j) \, F_{n-j},
$$

where $c(r, i)$ is the unsigned Stirling number of the first kind (the number of permutations of
$r$ elements with exactly $i$ cycles) and $F_m$ is the $m$-th Fubini number.

The proof follows Schreyer's: the signed falling-factorial expansion is evaluated at integers and
transported to surjection counts by image decomposition and binomial inversion, rather than by
shift operators.

## Sources

- Benjamin Schreyer, "Rigged Horse Numbers and their Modular Periodicity," Journal of Integer Sequences 28 (2025), Article 25.4.1, Theorem, lines 211–215, https://cs.uwaterloo.ca/journals/JIS/VOL28/Schreyer/schreyer7.tex
