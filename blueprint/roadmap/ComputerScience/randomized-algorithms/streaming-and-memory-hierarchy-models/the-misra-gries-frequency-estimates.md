# The Misra–Gries frequency estimates

Let $\sigma = a_1 \cdots a_m$ be a stream of tokens from $[n]$, with frequencies $f_j = |\{i : a_i = j\}|$, and let $k \ge 1$ be an integer. The *Misra–Gries* algorithm keeps an associative array $A$ of at most $k - 1$ counters. On each token $j$:
- if $j$ has a counter, increment it;
- otherwise, if fewer than $k - 1$ counters exist, create $A[j] = 1$;
- otherwise, decrement every counter and delete those that reach $0$.

Afterwards, the estimate for a token $a$ is $\hat f_a = A[a]$ if $a$ has a counter, and $0$ otherwise.

**Theorem.** In one pass and $O(k(\log m + \log n))$ bits of space, Misra–Gries computes estimates with

$$
f_a - \frac{m}{k} \le \hat f_a \le f_a \qquad \text{for every } a \in [n].
$$

In particular, every token with $f_a > m/k$ retains a counter, so a second pass that counts the at most $k - 1$ candidates exactly finds all such tokens.

**Proof.** Every increment of $A[a]$ corresponds to an occurrence of $a$, which gives $\hat f_a \le f_a$. Count the third case, in which the token is not stored, as an increment of its own counter from $0$ to $1$ followed by a decrement. Then every decrement step lowers exactly $k$ counters by one, each by one occurrence. Since at most $m$ increments happen, there are at most $m/k$ decrement steps. So $a$ loses at most $m/k$ of its occurrences.

## Depends on

- [Frequency of an element in a stream](../frequency-moments-of-data-streams/freq.md)

## Sources

- A. Chakrabarti, *Data Stream Algorithms*, lecture notes, Dartmouth College (update of 1 July 2025), <https://www.cs.dartmouth.edu/~ac/Teach/data-streams-lecnotes.pdf>, Unit 1: Algorithm 1 (Misra–Gries with at most $k - 1$ counters), Algorithm 2 (the thought experiment used in the analysis), Theorem 1.3.1 (one pass, $O(k(\log m + \log n))$ bits, $f_j - m/k \le \hat f_j \le f_j$), and Section 1.4 (finding the frequent items with a second pass).
