# Hoey–Sloane words

Let $n$ and $b$ be natural numbers. An input string
$(d_0, \hat d_0) \cdots (d_k, \hat d_k)$ of pairs of natural numbers belongs to the language $L$
of the $(n, b)$-Hoey–Sloane machine when, with $c_0, \dots, c_{k+1}$ the carries of the machine
on this string, every input $(d_j, \hat d_j)$ is an edge of the $(n, b)$-mother graph, $b$
divides $n \hat d_j - d_j + c_j$ for every $0 \le j \le k$, and $c_{k+1} = 0$.

So the walk starts in the state $c_0 = 0$, every transition is an exact division, and the walk
ends in the state $0$.

## Sources

- B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025), Article A13, Section 4 (the language `L` and `L`-walks).
