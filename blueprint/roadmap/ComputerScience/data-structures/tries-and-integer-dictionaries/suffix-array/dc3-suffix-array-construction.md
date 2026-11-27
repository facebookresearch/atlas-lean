# Suffix-array construction by the DC3 algorithm

Let $T$ be a text over a linearly ordered alphabet $\Sigma$, and let $\mathrm{sort}(\Sigma)$ be the
time needed to sort the letters of $T$. The DC3 (difference cover modulo $3$) algorithm of
Kärkkäinen and Sanders computes the [suffix array](suffix-array.md) of $T$ in
$O(|T| + \mathrm{sort}(\Sigma))$ time on a
[word RAM](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md).

## Proof sketch

Sort the letters of $T$ and replace each by its rank among them, so that the alphabet has at most
$|T|$ letters; this costs $O(\mathrm{sort}(\Sigma))$ time. Group the text into triples of letters
starting at positions $3i$, $3i + 1$ and $3i + 2$, giving texts $T_0$, $T_1$ and $T_2$ of about
$|T|/3$ letters each over the alphabet of triples. Radix-sort the triples in linear time and
recurse on the concatenation of $T_0$ and $T_1$, which has about $2|T|/3$ letters; this sorts the
suffixes of $T$ starting at positions $3i$ and $3i + 1$. A suffix starting at $3i + 2$ is its first
letter followed by a suffix starting at $3i + 3$, whose rank is known, so a radix sort on these two
keys sorts the suffixes starting at positions $3i + 2$ in linear time. Finally merge the two sorted
lists: a suffix starting at $3i$ or $3i + 1$ is compared with one starting at $3j + 2$ in constant
time, by comparing their first one or two letters and then two suffixes of the recursive call. The
time satisfies $t(n) = t(2n/3) + O(n)$, so $t(n) = O(n)$ after the initial sort of the alphabet.

## Depends on

- [Suffix array](suffix-array.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Cost bound for radix sort](../../../sorting-and-searching/radix-sort/radix-sort-time.md)

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 16 "Strings" (scribe notes, Spring 2012,
  revised 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec16.pdf>: Section 5,
  the DC3 algorithm in $O(|T| + \mathrm{sort}(\Sigma))$ time, steps 1 to 6 and the recurrence
  $T(n) = T(2n/3) + O(n)$, following J. Kärkkäinen and P. Sanders, *Simple linear work suffix
  array construction*, ICALP 2003, LNCS 2719, 943–955.
