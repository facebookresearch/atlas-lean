# Jowhari-Sağlam-Tardos samplers: zero-relative-error L0 sampling in O(log^2 n) bits

On turnstile streams over $[n]$ (with $M$ and the stream length at most $\mathrm{poly}(n)$) and constant failure probability $\delta$:

1. there is a zero-relative-error $L_0$ sampler, returning a uniformly random element of the support of $x$ up to additive error $n^{-c}$, together with its value, using $O(\log^2 n)$ bits; with failure probability $\delta$ it uses $O(\log^2 n \log(1/\delta))$ bits;
2. for $p \in (1, 2)$ there is an $O(\varepsilon)$-relative-error $L_p$ sampler with $O_p(\varepsilon^{-p}\log^2 n)$ bits; for $p \in (0, 1)$ with $O_p(\varepsilon^{-1}\log^2 n)$ bits; and for $p = 1$ with $O(\varepsilon^{-1}\log(1/\varepsilon)\log^2 n)$ bits; with failure probability $\delta$ each bound gains a factor $\log(1/\delta)$.

These improve the polylogarithmic-space samplers of Monemizadeh and Woodruff and the $O(\log^3 n)$-bit $L_0$ sampler of Frahling, Indyk and Sohler.

## Proof sketch

For $L_0$, first assume a random oracle. For $k = 0, 1, \dots, \lfloor\log n\rfloor$ let $I_k$ be a uniformly random subset of $[n]$ of size $2^k$ ($I_0 = [n]$), and run an exact $s$-sparse recovery structure with $s = \lceil 4\log(1/\delta)\rceil$ on $x$ restricted to $I_k$; each uses $O(s\log n)$ bits and either recovers an $s$-sparse vector exactly or reports that it is dense. Output a uniformly random nonzero coordinate of the first level that returns a nonzero $s$-sparse vector. Every support element is equally likely, and at the level where $|I_k \cap \mathrm{supp}(x)|$ is expected to be between $s/3$ and $2s/3$ a Chernoff bound gives success with probability $1 - \delta$. The random oracle is then replaced by Nisan's pseudorandom generator with an $O(\log^2 n)$-bit seed, which fools the logarithmic-space tests involved, for $O(\log^2 n\log(1/\delta))$ bits in total. For $p > 0$, precision sampling scales the coordinates by $t_i^{-1/p}$ for independent uniform $t_i \in (0, 1]$ and reports the coordinate that becomes heavy, found by a Count-Sketch structure, with $O(\log(1/\delta)/\varepsilon)$ parallel repetitions.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)
- [Approximate and perfect Lp samplers for turnstile streams](lp-samplers-in-turnstile-streams.md)

## Proof depends on

- [Exact 1-sparse recovery and detection with three linear counters](one-sparse-recovery-by-fingerprints.md)

## Sources

- Hossein Jowhari, Mert Sağlam, Gábor Tardos, "Tight Bounds for Lp Samplers, Finding Duplicates in Streams, and Related Problems", PODS (2011), arXiv:1012.4889.
- Morteza Monemizadeh, David P. Woodruff, "1-Pass Relative-Error Lp-Sampling with Applications", SODA (2010).
