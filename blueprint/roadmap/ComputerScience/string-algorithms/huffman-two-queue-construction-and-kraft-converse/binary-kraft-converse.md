# Constructive binary Kraft converse

For natural numbers $\ell_1, \dots, \ell_n$, there is a binary prefix-free code with codeword lengths $\ell_1, \dots, \ell_n$ if and only if $\sum_{i=1}^{n} 2^{-\ell_i} \le 1$. The code can be constructed by assigning codewords in order of nondecreasing length as the leftmost free nodes of the binary tree at the required depths, equivalently by taking the first $\ell_i$ bits of the binary expansion of $\sum_{j < i} 2^{-\ell_j}$ after sorting.

## Proof sketch

Necessity is Kraft's inequality. For sufficiency, after sorting, the partial sums $\sum_{j < i} 2^{-\ell_j}$ are multiples of $2^{-\ell_i}$ below $1$, and the corresponding dyadic intervals are disjoint, so their binary codewords are prefix-free.

## Depends on

- [Kraft's inequality for prefix codes](../../../InformationTheory/source-coding/kraft-mcmillan-lengths.md)
- [Prefix-free code](../../../InformationTheory/source-coding/prefix-codes/is-prefix-free.md)

## Sources

- L. G. Kraft, "A Device for Quantizing, Grouping, and Coding Amplitude-Modulated Pulses", MS thesis, Massachusetts Institute of Technology, 1949.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
