# Shuffle product of two words

For words $I = i_1 \cdots i_k$ and $J = j_1 \cdots j_m$, the shuffle product $I ⧢ J$ is the
multiset of the $\binom{k+m}{k}$ words obtained by interleaving $I$ and $J$ while keeping the
order of the letters of each, counted with multiplicity: for instance $i ⧢ i = \{ii, ii\}$, and
$121 ⧢ 23$ has ten entries. It is determined by $\varnothing ⧢ J = \{J\}$,
$I ⧢ \varnothing = \{I\}$ and the last-letter recursion

$$(I\,i) ⧢ (J\,j) = (I ⧢ J\,j)\,i \;+\; (I\,i ⧢ J)\,j .$$

Here $I ⧢ J$ is a finite list of words, with repetitions.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Definition 1.12, Example 1.13 and the remarks after it.
