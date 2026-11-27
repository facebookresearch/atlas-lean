# Count-Min sketch with binary linear hashing

Let each row of a Count-Min sketch use a hash $h_A(x) = A x$ over $\mathbb{F}_2$ from $n$-bit items to $m$-bit bucket indices ($2^m$ buckets), with $A$ a uniformly random $m \times n$ binary matrix, independently for each of $d$ rows (seed space of $2^{mnd}$ matrices). This family is universal. For a weighted insertion-only stream and a query item $x$, both fixed before the seeds are drawn, the estimate never underestimates the frequency $f_x$, and

$$
\Pr\left[\hat f_x > f_x + \varepsilon \|f\|_1\right] \le \left(\frac{1}{2^m \varepsilon}\right)^d ,
$$

so $2 \le 2^m \varepsilon$ gives failure probability at most $2^{-d}$. Tables built with the same hashes merge by entrywise addition, and every counter is at most the total stream weight.

## Proof sketch

For $x \ne y$, $Ax = Ay$ iff $A(x - y) = 0$, which happens with probability $2^{-m}$ since $A(x-y)$ is uniform. The expected collision noise in one row is at most $\|f\|_1 / 2^m$; Markov's inequality bounds one row's failure by $1/(2^m\varepsilon)$, and independent rows multiply.

## Depends on

- [The Count-Min sketch](../streaming-and-memory-hierarchy-models/the-count-min-sketch.md)
- [Frequency of an element in a stream](../frequency-moments-of-data-streams/freq.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Proof depends on

- [The Count-Min sketch](../streaming-and-memory-hierarchy-models/the-count-min-sketch.md)

## Sources

- G. Cormode and S. Muthukrishnan, "An Improved Data Stream Summary: The Count-Min Sketch and its Applications", Journal of Algorithms 55(1), 2005.
- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
