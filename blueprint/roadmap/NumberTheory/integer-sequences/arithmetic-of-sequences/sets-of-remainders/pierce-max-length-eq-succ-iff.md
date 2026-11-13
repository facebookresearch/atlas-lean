# Maximal Pierce length via iterated remainder sets

Let $n \ge 3$ and $t$ be natural
numbers, let $P(n)$ be the maximal Pierce length of $n$ and let $S_j(n)$ be the iterated
remainder sets of $n$. Then the following are equivalent: $P(n) = t + 1$; $S_t(n) = \{0\}$;
$S_t(n)$ has exactly one element and $S_{t+j}(n) = \emptyset$ for every $j \ge 1$.

This corrects the index of the printed lemma, $P(n) = t \iff S_{t+1}(n) = \{0\}$, which fails
for every $n \ge 3$: for example $P(5) = 3$, $S_2(5) = \{0\}$ and $S_4(5) = \emptyset$. The
paper derives the lemma from its Lemma 18 ($r \in S_j(n)$ if and only if $a_{j+1} = r$ for some
$\lfloor n/2 \rfloor + 1 \le a \le n$, where $a_0 = a$ and $a_{i+1} = n \bmod a_i$), which
gives the index $P(n) - 1$. Lemma 18, and hence this lemma, needs $n \ge 3$: $P(2) = 1$ but
$S_0(2) = \{1\}$.

## Sources

- the forward direction of the first equivalence (for `t ≥ 1`) is proved as `S_eq_singleton_zero_of_maxLength_eq` in `FormalizedPapers/NumberTheory/BaraskarGokhaleJainKiezun2026`.
- Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of Integer Sequences 29 (2026), Article 26.1.4, Lemma 19.
