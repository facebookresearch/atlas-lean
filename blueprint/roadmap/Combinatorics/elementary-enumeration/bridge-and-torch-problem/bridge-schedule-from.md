# Valid crossing sequences from a state of the bridge and torch problem

Let $c$ be a
natural number and let $P$ and $L$ be finite sets of natural numbers, the people and the left
bank. Whether a finite sequence $A_1, \dots, A_k$ of finite sets of natural numbers (the
crossings) is valid from the left bank $L$ with the torch on a given side is defined by recursion
on $k$. The empty sequence is valid exactly when $L = \emptyset$ and the torch is on the right.
With the torch on the left, the sequence is valid when $A_1$ is a nonempty subset of $L$ with at
most $c$ elements and $A_2, \dots, A_k$ is valid from the left bank $L \setminus A_1$ with the
torch on the right. With the torch on the right, it is valid when $A_1$ is a nonempty subset of
$P \setminus L$ with at most $c$ elements and $A_2, \dots, A_k$ is valid from the left bank
$L \cup A_1$ with the torch on the left.

## Sources

- Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6, proof of Theorem 1 (states and moves) and Section 3 (capacity `c`).
