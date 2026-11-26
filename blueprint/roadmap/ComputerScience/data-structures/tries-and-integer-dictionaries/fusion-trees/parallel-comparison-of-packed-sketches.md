# Parallel comparison of packed sketches

Pack $k$ sketches of $s$ bits into one word, each followed by a guard bit set to $1$, and replicate a query sketch $t$ into every field by multiplication with the all-fields-one constant. Then a single subtraction of the replicated query from the packed node word leaves, in each field, the guarded difference of that sketch and $t$, without borrows between fields, and the guard bit of a field is set exactly when $t \le$ that sketch. Hence the sketch rank of $t$ (the number of stored sketches below $t$) is obtained from the guard bits with $O(1)$ further instructions, provided $k(s + 1) \le w$.

## Proof sketch

Each field of the packed word holds $2^s + \mathrm{sketch}_i \ge t$ before subtraction, so every field difference is nonnegative and fits in $s + 1$ bits; its top bit is $1$ iff $\mathrm{sketch}_i \ge t$. Masking the guards and counting them (by multiplication or a most-significant-bit computation) gives the rank.

## Depends on

- [Significant bits and perfect sketch of a key set](perfect-sketch-of-a-key-set.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
