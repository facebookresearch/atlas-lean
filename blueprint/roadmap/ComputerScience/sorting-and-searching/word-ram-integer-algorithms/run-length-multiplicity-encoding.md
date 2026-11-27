# Run-length multiplicity encoding of a multiset

For a finite list $x$ of natural numbers, a **run-length multiplicity encoding** of $x$ is a list of pairs $(k_1, c_1), \dots, (k_r, c_r)$ with $k_1 < k_2 < \dots < k_r$ and every $c_j \ge 1$ such that expanding each pair into $c_j$ copies of $k_j$ yields the sorted rearrangement of $x$. Such an encoding exists and is unique: $\{k_1, \dots, k_r\}$ is the set of distinct values of $x$ and $c_j$ is the multiplicity of $k_j$.

## Depends on

- [Radix sort](../radix-sort/radix-sort.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd ed., Addison-Wesley, 1998.
