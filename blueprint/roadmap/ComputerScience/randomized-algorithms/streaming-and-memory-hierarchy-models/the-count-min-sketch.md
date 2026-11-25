# The Count-Min sketch

Let $0 < \varepsilon, \delta < 1$. A stream consists of updates $(j, c)$ with $j \in [n]$ and a positive integer $c$, the *cash-register* model, and the frequency $f_j$ is the total weight of the updates to $j$. Write $\|f_{-a}\|_1 = \sum_{j \ne a} f_j$.

The *Count-Min sketch* keeps a $t \times k$ array $C$ of counters, with $k = \lceil 2/\varepsilon \rceil$ and $t = \lceil \log_2(1/\delta) \rceil$, and $t$ hash functions $h_1, \dots, h_t : [n] \to [k]$ drawn independently from a 2-universal family.
- Each update $(j, c)$ adds $c$ to $C[i][h_i(j)]$ for every row $i$.
- The estimate for $a$ is $\hat f_a = \min_i C[i][h_i(a)]$.

**Theorem.** For every $a$:
1. $\hat f_a \ge f_a$ always;
2. $\Pr\bigl[\hat f_a > f_a + \varepsilon \|f_{-a}\|_1\bigr] \le \delta$;
3. the sketch uses $O(\varepsilon^{-1} \log(1/\delta) \cdot (\log m + \log n))$ bits, where $m$ bounds the total weight of the stream.

**Proof.**
1. Every counter that $a$ hashes to has received all of $a$'s weight, and all weights are positive.
2. The excess $X_i = \sum_{j \ne a} f_j [h_i(j) = h_i(a)]$ in row $i$ is nonnegative, and has expectation at most $\|f_{-a}\|_1/k$ by 2-universality. If $\|f_{-a}\|_1 = 0$, every excess is $0$. Otherwise Markov's inequality gives $\Pr[X_i > \varepsilon\|f_{-a}\|_1] \le 1/(k\varepsilon) \le 1/2$. The rows are independent, so the minimum excess exceeds $\varepsilon\|f_{-a}\|_1$ with probability at most $2^{-t} \le \delta$.

## Depends on

- [Frequency of an element in a stream](../frequency-moments-of-data-streams/freq.md)

## Background

- [The Misra–Gries frequency estimates](the-misra-gries-frequency-estimates.md)

## Sources

- A. Chakrabarti, *Data Stream Algorithms*, lecture notes, Dartmouth College (update of 1 July 2025), <https://www.cs.dartmouth.edu/~ac/Teach/data-streams-lecnotes.pdf>, Section 5.4: Algorithm 9 (the Count-Min sketch with $k = 2/\varepsilon$ columns, $t = \lceil \log(1/\delta) \rceil$ rows, and independent 2-universal hash functions), and Section 5.4.1 (the overestimate in the cash-register model, $\mathbb{E} X_i = \|f_{-a}\|_1/k$, Markov's inequality, independence of the rows, and the space bound).
