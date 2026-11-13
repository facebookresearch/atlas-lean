# Table of Gutkovskiy's sequence

The Gutkovskiy tables $T_0, T_1, \dots$ are finite lists
of natural numbers, indexed from $0$, defined by $T_0 = [0]$ and, for $n \ge 0$, $T_{n+1}$ is
$T_n$ with the entry $(n + 1) - T_n[\lfloor T_n[n]/2 \rfloor]$ appended at the end. Here $T_n[j]$
is the entry of $T_n$ at index $j$, or $0$ if $T_n$ has fewer than $j + 1$ entries, and the
subtraction is truncated at $0$.

$T_n$ has $n + 1$ entries and lists the terms $g_0, \dots, g_n$ of Gutkovskiy's sequence, so each
step reads only values already computed.

## Sources

- Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24 (2024), Article A51, Section 1, Equation (1).
