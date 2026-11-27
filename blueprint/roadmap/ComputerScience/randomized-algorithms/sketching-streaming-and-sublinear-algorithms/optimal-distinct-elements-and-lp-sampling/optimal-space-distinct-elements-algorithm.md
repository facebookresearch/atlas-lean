# Kane-Nelson-Woodruff distinct-elements algorithm with O(1/eps^2 + log n) bits

For $0 < \varepsilon < 1$, the *$(\varepsilon, \delta)$-distinct elements problem* asks, for an insertion-only stream over $[n]$, to output at query time an estimate $\widetilde{F}_0$ with

$$
\Pr\big[\,|\widetilde{F}_0 - F_0| \le \varepsilon F_0\,\big] \ge 1 - \delta.
$$

For $\delta = 1/3$ there is a one-pass randomized algorithm using $O(\varepsilon^{-2} + \log n)$ bits of space, with $O(1)$ worst-case update time and $O(1)$ worst-case reporting time on a word RAM with $\Theta(\log n)$-bit words; an estimate can be reported at any point mid-stream.

## Proof sketch

A constant-factor estimator run in parallel selects a subsampling level at which roughly $\varepsilon^{-2}$ distinct hashed elements survive. At that level the survivors are thrown into $K = \Theta(\varepsilon^{-2})$ bins, each bin storing only a small offset of the least significant set bit of a second hash, and the offsets are compressed with a variable-length encoding into $O(1)$ bits per bin on average. The estimate inverts the expected number of occupied bins, a balls-into-bins computation whose variance is controlled with limited-independence hash families, and careful word-level bookkeeping gives constant update and reporting times.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Proof depends on

- [Constant-factor estimation of the number of distinct elements](../../streaming-and-memory-hierarchy-models/constant-factor-estimation-of-the-number-of.md)
- [Universal hash family](../../../data-structures/hashing/universal-hashing/is-universal.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)
- [Chebyshev's inequality](../../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)

## Sources

- Daniel M. Kane, Jelani Nelson, David P. Woodruff, "An Optimal Algorithm for the Distinct Elements Problem", PODS (2010).
