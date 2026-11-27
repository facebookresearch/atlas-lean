# The Klee-Minty program

The $n$-dimensional **Klee-Minty program** (in the form presented by Chvátal) is

$$
\max \sum_{j=1}^{n} 10^{\,n-j} x_j \quad \text{s.t.} \quad 2\sum_{j=1}^{i-1} 10^{\,i-j} x_j + x_i \le 100^{\,i-1} \ (1 \le i \le n), \quad x \ge 0,
$$

a perturbed cube whose feasible region has $2^n$ vertices.

## Depends on

- [Simplex dictionaries and pivoting](simplex-dictionaries.md)

## Sources

- V. Klee and G. J. Minty, "How Good is the Simplex Algorithm?", in O. Shisha (ed.), Inequalities III, Academic Press, 1972.
- V. Chvátal, "Linear Programming", W. H. Freeman, 1983.
