# Suffix-array construction by the DC3 algorithm

Let $T$ be a text over a linearly ordered alphabet $\Sigma$, and let $\mathrm{sort}(\Sigma)$ be the
time needed to sort the letters of $T$. The DC3 (difference cover modulo $3$) algorithm of
Kärkkäinen and Sanders computes the [suffix array](suffix-array.md) of $T$ in
$O(|T| + \mathrm{sort}(\Sigma))$ time on a
[word RAM](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md).

## Proof sketch

Sort the letters of $T$ and replace each by its rank among them, so that, with $n = |T|$, the
letters are integers in $\{1, \dots, n\}$; this costs $O(\mathrm{sort}(\Sigma))$ time. Pad $T$ with
$T[n] = T[n + 1] = T[n + 2] = 0$, a letter smaller than every other. The sample positions are the
$i < n$ with $i \not\equiv 0 \pmod 3$, together with $i = n$ when $n \equiv 1 \pmod 3$. Radix-sort
the triples $T[i]\,T[i + 1]\,T[i + 2]$ at the sample positions in linear time and name each by its
rank among the distinct triples. Let $R = R_1 R_2$, where $R_1$ lists the names of the sample
positions $i \equiv 1$ and $R_2$ those of the sample positions $i \equiv 2 \pmod 3$, each in
increasing order of $i$; $R$ has about $2n/3$ letters. From the name of a sample position $i$ to the
end of its part, $R_1$ or $R_2$, the names spell in triples the suffix of $T$ starting at $i$,
padded with zeros. The last name in $R_1$ is that of a position $i \ge n - 2$, and its triple is the
only one in $R$ whose first $0$ is at offset $n - i$; so this name occurs once in $R$, every
comparison of two suffixes of $R$ is decided before either leaves $R_1$, and the order of the
suffixes of $R$ is that of the suffixes of $T$ at the sample positions. If the names are all
distinct, as when $n \le 2$, which leaves at most one sample position, that order is the order of
the names; otherwise sort the suffixes of $R$ recursively. The dummy position $n$, when sampled,
stands for the empty suffix, which comes first; drop it from the sorted sample before the merge, so
that the result has $n$ entries. A suffix starting at $i \equiv 0 \pmod 3$ is its first letter
followed by the suffix starting at the sample position $i + 1$, so one radix sort on these pairs
sorts the suffixes starting at positions $i \equiv 0$ in linear time. Finally merge the two sorted
lists: a suffix starting at $j \equiv 0$ is compared with one starting at $i \equiv 1$ through their
first letters and the suffixes starting at $j + 1$ and $i + 1$, and with one starting at
$i \equiv 2$ through their first two letters and the suffixes starting at $j + 2$ and $i + 2$. These
are at sample positions, or empty, which ranks first, so each comparison takes constant time. The
time satisfies $t(n) = t(2n/3) + O(n)$, with $t(n) = O(1)$ for $n < 3$, so $t(n) = O(n)$ after the
initial sort of the alphabet.

## Comparison with the source

Demaine's notes recurse on the concatenation of the triples starting at positions $3i$ and at
positions $3i + 1$, with no rule at the boundary between the two parts, and the recursion can then
misorder suffixes: for $T = aaaaaa$, padded with $0$, and $A = aaa$ and $B = aa0 < A$, the triples
at positions $0, 3$ and $1, 4$ give $AAAB$, whose suffixes at the names of positions $1$ and $3$ are
$AB < AAB$, although the suffix $aaa$ at position $3$ is smaller than the suffix $aaaaa$ at position
$1$. The sketch above follows Kärkkäinen and Sanders, who sample the positions
$i \not\equiv 0 \pmod 3$ and pad the text so that the last name of the first part is unique.

## Depends on

- [Suffix array](suffix-array.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Cost bound for radix sort](../../../sorting-and-searching/radix-sort/radix-sort-time.md)

## Sources

- J. Kärkkäinen and P. Sanders, *Simple linear work suffix array construction*, ICALP 2003, LNCS
  2719, 943–955, <https://www.cs.helsinki.fi/u/tpkarkka/publications/icalp03.pdf>: Section 2, the
  skew algorithm, which sorts the suffixes at the positions $i \not\equiv 0 \pmod 3$ recursively
  through the names of their triples, with zeros after the end of the text, sorts and merges the
  others, and runs in $O(n)$ time (Theorem 1); its appendix pads the text with three zeros, recurses
  only when two sample triples get the same name, and adds a dummy sample position when
  $n \equiv 1 \pmod 3$, which its merge skips.
- E. Demaine, *6.851: Advanced Data Structures*, Lecture 16 "Strings" (scribe notes, Spring 2012,
  revised 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec16.pdf>: Section 5,
  the DC3 algorithm in $O(|T| + \mathrm{sort}(\Sigma))$ time, steps 1 to 6 and the recurrence
  $T(n) = T(2n/3) + O(n)$, following Kärkkäinen and Sanders.
