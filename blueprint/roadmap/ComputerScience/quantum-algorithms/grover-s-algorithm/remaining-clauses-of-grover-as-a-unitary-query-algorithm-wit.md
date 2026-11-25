# Grover's algorithm as a query algorithm with $t$ marked items

The amplitude dynamics of Grover's algorithm in the two-dimensional invariant plane are separate pages, including the
one listed under the proof dependencies. This node collects the query-model statements they do not supply.

## Expansion

A sound expansion has separate pages for:

1. **Query-model instantiation.** For $N = 2^n$ and $x \in \{0,1\}^N$ with phase oracle $O_x$, the Grover iterate
   $-H^{\otimes n} O_0 H^{\otimes n} O_x$, with $O_0 = I - 2\lvert 0 \rangle\langle 0 \rvert$, uses one query and acts on real amplitude
   vectors, in particular on the span of the uniform superpositions over marked and unmarked indices, as the real-amplitude
   Grover step (phase oracle followed by inversion about the mean).
2. **Known marked count.** If the number $t = |x|$ of marked indices satisfies $1 \le t \le N$ and is known, then with
   $\theta = \arcsin\sqrt{t/N}$, $k = \lfloor \pi/(4\theta) \rfloor \le (\pi/4)\sqrt{N/t}$ iterations followed by a measurement return a
   marked index with probability at least $\max(1 - t/N, t/N)$.
3. **Unknown marked count.** An expected $O(\sqrt{N/t})$ queries suffice for $t \ge 1$, by a randomized schedule, as a separate
   statement; $t = 0$ is detected only with a stated failure convention.

## Depends on

- [Run of a query algorithm](../lower-bound-for-quantum-search/query-run.md)
- [Phase oracle](../deutsch-jozsa-and-bernstein-vazirani-algorithms/phase-oracle.md)

## Proof depends on

- [Symmetric amplitude vector](symmetric-amplitude.md)
- [Exact success probability of Grover search](marked-probability-grover-iterate-unifor.md)
- [Standard Grover iteration count](floor-iterations.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §7.2 (the Grover iterate as two reflections, success probability $\sin^2((2k+1)\theta)$, $k \le (\pi/4)\sqrt{N/t}$, and the unknown-$t$ variant with expected $O(\sqrt{N/t})$ queries). <https://arxiv.org/pdf/1907.09415v6>
- G. Brassard, P. Høyer, M. Mosca and A. Tapp, "Quantum amplitude amplification and estimation", arXiv:quant-ph/0005055, Theorem 2 with $\mathcal{A} = H^{\otimes n}$ ($m = \lfloor \pi/4\theta_a \rfloor$ gives success at least $\max(1 - a, a)$). <https://arxiv.org/abs/quant-ph/0005055>
