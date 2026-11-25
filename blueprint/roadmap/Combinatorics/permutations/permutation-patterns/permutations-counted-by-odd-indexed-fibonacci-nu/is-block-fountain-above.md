# Rows of coins stacked as a block fountain

For natural numbers $a, l$ and a list of rows $(a_1, l_1), (a_2, l_2), \dots, (a_m, l_m)$ of pairs of natural numbers, the rows form a block fountain above the row $(a, l)$ (a row of $l$ coins at positions $a, \dots, a + l - 1$) when, recursively:

- the empty list is always a block fountain above $(a, l)$;
- the list $(a_1, l_1), (a_2, l_2), \dots$ is a block fountain above $(a, l)$ when $a \le a_1$, $l_1 \ge 1$, $a_1 + l_1 + 1 \le a + l$, and $(a_2, l_2), \dots$ is a block fountain above $(a_1, l_1)$.

Each row is a nonempty contiguous block whose coin at position $p$ rests on the coins at positions $p$ and $p + 1$ of the row beneath. A block $n$-fountain is a list of rows forming a block fountain above $(0, n)$.

## Sources

- Juan B. Gil, Felix H. Xu, and William Y. Zhu, "Odd-Indexed Fibonacci Numbers via Pattern-Avoiding Permutations", *INTEGERS* 25 (2025), Article A79, Section 3.1 (block $n$-fountains).
