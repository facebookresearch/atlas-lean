# Reduction of a sequence

The reduction $\operatorname{red}(s)$ of a finite sequence $s$ of
natural numbers is obtained in two steps. First, every maximal block of adjacent entries of the
form $a, a + 1, \ldots, a + k$ is replaced by its first entry $a$. Then the resulting sequence is
standardized: each of its entries $x$ is replaced by the number of its entries that are at most
$x$, which for distinct entries is the rank of $x$.

## Sources

- Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026), Article A15, Section 2.
