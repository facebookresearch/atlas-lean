# Distinct-position 3SUM as finitely many three-set problems

Call $(P, Q, R)$ a **three-set instance** if $P, Q, R$ are finite sets of integers, with solution any $(p, q, r) \in P \times Q \times R$ with $p + q + r = 0$. A list $x = (x_1, \dots, x_n)$ of integers (repetitions allowed) has a **distinct-position 3SUM solution** if there are pairwise distinct positions $i, j, k$ with $x_i + x_j + x_k = 0$. Let $v_0 < \dots < v_{k-1}$ be the distinct values of $x$ ($k \le n$), let $L = \lceil \log_2 \max(n, 2) \rceil$, and write $r_\beta$ for bit $\beta$ of the binary expansion of $r$. For $\beta, \gamma < L$ and $e \in \{0, 1\}$, let $I^0_{\beta\gamma e} = (P, Q, R)$ with $P = \{v_r : r_\beta = 0, r_\gamma = e\}$, $Q = \{v_r : r_\beta = 1\}$, $R = \{v_r : r_\beta = 0, r_\gamma = 1 - e\}$, and let $I^1_{\beta\gamma e}$ be the same with the roles of the bit values of $r_\beta$ exchanged. Then $x$ has a distinct-position 3SUM solution if and only if one of the following holds: (i) the value $0$ occurs at least three times; (ii) some value $v$ occurs at least twice and $-2v \ne v$ also occurs; (iii) one of the $4L^2$ three-set instances $I^d_{\beta\gamma e}$ has a solution. All these sets have size at most $n$ and entries of absolute value at most $\max_i |x_i|$.

## Proof sketch

Classify a solution by how many of its three values coincide: three equal values force $v = 0$, exactly two equal values $v$ force the third to be $-2v \ne v$, and three distinct values $v_a, v_b, v_c$ have pairwise distinct ranks. Pick a bit $\beta$ where $a$ and $b$ differ; $c$ differs at $\beta$ from one of them and, at some bit $\gamma$, from the other, which places the three values in some $I^d_{\beta\gamma e}$. Conversely, a solution of $I^d_{\beta\gamma e}$ has pairwise distinct ranks, hence three distinct values at distinct positions, and (i) or (ii) give solutions directly.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
