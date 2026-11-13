# Fuel-bounded enumeration of alignments

Given a fuel $n \in \mathbb{N}$ and sequences
$x$ and $y$ over $\alpha$, this lists alignments column by column from the front. With fuel $0$
the list is empty. With fuel $n + 1$: two empty sequences give the single empty alignment; if
only $y$ is nonempty, with first letter $b$ and rest $y'$, each alignment of $x$ and $y'$ with
fuel $n$ is preceded by the column pairing a gap with $b$; if only $x$ is nonempty, with first
letter $a$ and rest $x'$, each alignment of $x'$ and $y$ with fuel $n$ is preceded by the
column pairing $a$ with a gap; and if both are nonempty, $x$ with first letter $a$ and rest $x'$
and $y$ with first letter $b$ and rest $y'$, the list consists of the alignments of $x'$ and
$y'$ preceded by the column $(a, b)$, then those of $x'$ and $y$ preceded by the column pairing
$a$ with a gap, then those of $x$ and $y'$ preceded by the column pairing a gap with $b$, each
computed with fuel $n$.

With fuel at least $|x| + |y| + 1$ the fuel never runs out before both sequences are used up;
with less fuel some alignments are missing from the list.
