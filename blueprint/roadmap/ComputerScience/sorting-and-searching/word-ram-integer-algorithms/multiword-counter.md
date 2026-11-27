# Multiword counters on the word RAM

Represent a natural number $N$ by its little-endian base-$2$ digit list $d_0, \dots, d_{\ell-1}$ stored one digit per memory word. There are word-RAM routines that

1. replace $N$ by $aN + b$ for word-sized $a, b$ in $O(\ell + \log_2(a+b+1))$ instructions, producing a digit list of length at most $\ell + \lceil \log_2 (a + b + 1) \rceil + 1$;
2. decrement a positive counter and test it for zero in $O(\ell)$ instructions.

In particular a number such as $\lceil (3n+1)\,(4/3)^n \rceil$, which needs $\Theta(n)$ bits and so does not fit one word of size $O(\log n)$, can be built by $O(n)$ multiply-add steps in $O(n^2)$ instructions and used as a loop counter with $O(n)$ instructions per decrement.

## Proof sketch

Schoolbook multiply-add with a carry word: each digit position produces one output digit and a carry bounded by $a + b$, so the carry fits in a word and the length grows only by the carry's bit length.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", 3rd ed., Addison-Wesley, 1997, Section 4.3.1.
- U. Schöning, "A Probabilistic Algorithm for k-SAT and Constraint Satisfaction Problems", 40th IEEE Symposium on Foundations of Computer Science (FOCS), 1999.
