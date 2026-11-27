# Jowhari-Sağlam-Tardos samplers: zero-relative-error L0 sampling in O(log^2 n) bits

On turnstile streams over $[n]$ (with $M$ and the stream length at most $\mathrm{poly}(n)$) and constant failure probability $\delta$:

1. there is a zero-relative-error $L_0$ sampler, returning a uniformly random element of the support of $x$ up to additive error $n^{-c}$, together with its value, using $O(\log^2 n)$ bits; with failure probability $\delta$ it uses $O(\log^2 n \log(1/\delta))$ bits;
2. for $p \in (1, 2)$ there is an $\varepsilon$-relative-error $L_p$ sampler with $O(\varepsilon^{-p}\log^2 n)$ bits; for $p \in (0, 1)$ with $O(\varepsilon^{-1}\log^2 n)$ bits; and for $p = 1$ with $O(\varepsilon^{-1}\log(1/\varepsilon)\log^2 n)$ bits.

These improve the polylogarithmic-space samplers of Monemizadeh and Woodruff and the $O(\log^3 n)$-bit $L_0$ sampler of Frahling, Indyk and Sohler.

## Proof sketch

For $L_0$, subsample the coordinates at $\log n$ geometric levels with a hash function of limited independence, so that at the level where about $s = \Theta(\log(1/\delta))$ support elements survive, an $s$-sparse recovery structure recovers all survivors exactly; outputting the survivor with the smallest hash value is uniform. Using $s$-sparse recovery instead of 1-sparse recovery at each level, with sketches of $O(s \log n)$ bits, gives the $O(\log^2 n)$ total for constant $\delta$. For $p > 0$, scale coordinates by $t_i^{-1/p}$ for independent uniform $t_i \in (0, 1]$ and report the coordinate that becomes heavy, found by a Count-Sketch-type heavy hitters structure.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)
- [Approximate and perfect Lp samplers for turnstile streams](lp-samplers-in-turnstile-streams.md)

## Proof depends on

- [Exact 1-sparse recovery and detection with three linear counters](one-sparse-recovery-by-fingerprints.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Hossein Jowhari, Mert Sağlam, Gábor Tardos, "Tight Bounds for Lp Samplers, Finding Duplicates in Streams, and Related Problems", PODS (2011), arXiv:1012.4889.
- Morteza Monemizadeh, David P. Woodruff, "1-Pass Relative-Error Lp-Sampling with Applications", SODA (2010).
