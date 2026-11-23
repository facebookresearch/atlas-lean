# Sorting by reversals

Permutations of $1, \dots, n$ are written as lists of integers, with positions counted from $0$,
and framed by $0$ on the left and $n + 1$ on the right. A breakpoint is an adjacent pair of the
framed list that is not consecutive: two entries that are not one apart in the unsigned setting,
and a pair $(a, b)$ with $b - a \ne 1$ in the signed setting, where a reversal also changes the
signs of the reversed entries. For permutations, unsigned or signed, a reversal of a block inside
the list changes the number of breakpoints by at most two, so for every permutation $\pi$ of
$1, \dots, n$ the number of breakpoints is at most twice the reversal distance,
$b(\pi) \le 2\,d(\pi)$. Doubling each signed entry, $+a$ to $(2a - 1, 2a)$ and $-a$ to
$(2a, 2a - 1)$, turns a signed permutation into an unsigned one with the same number of
breakpoints. The pages follow Shamir and Peer, *Algorithms for Molecular Biology*, Lecture 11.

## Unsigned permutations, reversals and sorting

- [Increasing list of the natural numbers from m to n](icc.md)
- [Permutation of 1, …, n as a list of integers](uvalid.md)
- [Reversal of the block of positions i to j of a list](rev-block.md)
- [A reversal of positions inside the list preserves its length](rev-block-length.md)
- [A reversal of positions inside the list rearranges it](rev-block-perm.md)
- [A reversal inside a permutation of 1, …, n gives another one](rev-block-valid.md)
- [A reversal inside a list leaves an appended last entry in place](rev-block-append-singleton.md)
- [Sorting a list by exactly k reversals](usortable-in.md)
- [Appending n + 1 preserves sortability in exactly k reversals](usortable-in-succ-append.md)
- [Every permutation of 1, …, n can be sorted by reversals](sortable.md)
- [Unsigned reversal distance of a permutation of 1, …, n](udist.md)

## Unsigned breakpoints and the lower bound

- [Indicator that two integers are not one apart](is-gap.md)
- [Number of adjacent pairs whose absolute difference is not one](gap-count.md)
- [Unsigned breakpoint count of a list framed by 0 and n + 1](ubreaks.md)
- [The identity permutation has no breakpoints](ubreaks-target.md)
- [Sortable in k reversals implies at most 2k breakpoints](ubreaks-le-two-mul-of-sortable-in.md)
- [Unsigned breakpoints are at most twice the unsigned reversal distance](ub-le-two-mul-udist.md)
- [The identity is the only permutation of 1, …, n with no breakpoints](ubreaks-eq-zero-iff.md)
- [Unsigned reversal distance is 0 exactly for the identity](udist-eq-zero-iff.md)

## Signed permutations and signed reversals

- [Signed permutation of 1, …, n](svalid.md)
- [Lists whose entries have absolute values between 1 and n](mem-range.md)
- [Entries of a signed permutation have absolute values from 1 to n](svalid-imp-mem-range.md)
- [Entries of a signed permutation have distinct absolute values](svalid-imp-nodup.md)
- [Signed reversal of the block of positions i to j of a list](srev-block.md)
- [Signed reversals inside the list preserve signed permutations](srev-block-valid.md)
- [Sorting a list by exactly k signed reversals](ssortable-in.md)
- [Every signed permutation can be sorted by signed reversals](ssortable.md)
- [Signed reversal distance of a signed permutation](sdist.md)

## Signed breakpoints and doubling

- [Indicator that the second integer is not the first plus one](is-dir-gap.md)
- [Number of adjacent pairs that are not an increase by one](dir-gap-count.md)
- [Signed breakpoint count of a list framed by 0 and n + 1](sbreaks.md)
- [Doubling of a signed entry into a pair of consecutive integers](dbl-one.md)
- [First entry of the doubled pair of an integer](dbl-first.md)
- [Second entry of the doubled pair of an integer](dbl-last.md)
- [Doubling a list of signed integers](dbl.md)
- [Doubling a list doubles its length](dbl-length.md)
- [Doubling plus or minus n + 1 gives 2n + 1 and 2n + 2 in some order](dbl-one-perm-target-ext.md)
- [The two entries of a doubled pair differ by one](inside-gap.md)
- [Junction gap is unchanged by doubling for distinct nonzero magnitudes](between-gap.md)
- [Left-end gap is unchanged by doubling for a nonzero entry](left-gap.md)
- [Right-end gap is unchanged by doubling for absolute value at most n](right-gap.md)
- [Directed gap from 0 to n + 1 equals the gap from 0 to 2n + 1](empty-gap.md)
- [Directed gaps of a partial signed permutation equal its doubled gaps](aux-correspondence.md)
- [For signed permutations, signed breakpoints equal doubled breakpoints](sbreaks-eq-ubreaks-dbl-of-valid.md)
- [Signed breakpoints of a list can differ from those of its doubling](sbreaks-eq-ubreaks-dbl-counterex.md)
- [On signed permutations, doubling turns signed into unsigned reversals](dbl-srev-block.md)

## Signed breakpoints and the lower bound

- [Signed reversals inside signed permutations add at most 2 breakpoints](sbreaks-srev-block-le.md)
- [Signed reversals remove at most two breakpoints of signed permutations](sbreaks-le-srev-block.md)
- [Sortable in k signed reversals implies at most 2k signed breakpoints](sbreaks-le-two-mul-of-ssortable-in.md)
- [Signed breakpoints are at most twice the signed reversal distance](sb-le-two-mul-sdist.md)
- [The identity is the only signed permutation with no signed breakpoints](sbreaks-eq-zero-iff.md)
- [Signed reversal distance is 0 exactly for the identity](sdist-eq-zero-iff.md)

## Identity lists and framed lists

- [The list 1, …, n + 1 of natural numbers is 1, …, n followed by n + 1](icc-one-succ.md)
- [The list 1, …, n + 1 of natural numbers contains n + 1](mem-icc-self-succ.md)
- [Every entry of the list 1, …, n lies between 1 and n](mem-icc-bounds.md)
- [The list 1, …, n has no repeated entries](icc-nodup.md)
- [The integer list 1, …, n + 1 is 1, …, n followed by n + 1](target-succ.md)
- [The integer list 1, …, 2n + 2 is 1, …, 2n followed by 2n + 1, 2n + 2](target-double-succ.md)
- [The identity list 1, …, n has length n](target-length.md)
- [The integer list 1, …, n + 1 contains n + 1](mem-target-succ.md)
- [Entries of the identity list are natural numbers at most n](mem-target-upper.md)
- [The framed identity of size n + 1 extends that of size n by n + 2](framed-succ.md)
- [The framed identity list ends with n + 1](framed-get-last.md)
- [Prepending 0 to a list ending in x leaves x as the last entry](framed-init-get-last.md)

## Integers, lists and gaps

- [A nonempty list is a list followed by one last entry](exists-init-last.md)
- [A list containing x is a rearrangement of x followed by a list](exists-perm-cons-of-mem.md)
- [No gaps in a concatenation means none in the parts or at the junction](gap-count-append-eq-zero.md)
- [The integers n + 1 and n + 2 form no gap](is-gap-consec.md)
- [The gap indicator vanishes exactly when the integers are one apart](is-gap-eq-zero-iff.md)
- [An integer one apart from k + 1 is k or k + 2](is-gap-up-cases.md)
- [An integer has absolute value one exactly when it is 1 or −1](nat-abs-eq-one-iff.md)
- [The absolute value of a nonnegative integer is itself](nat-abs-cast-of-nonneg.md)
- [The absolute value of a negative integer is its negation](nat-abs-cast-of-neg.md)
