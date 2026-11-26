# The edge tester for monotonicity of Boolean functions

For $f : \{0,1\}^n \to \{0,1\}$ let an edge $\{x, x \oplus e_i\}$ with $x_i = 0$ be *violated* if $f(x) > f(x \oplus e_i)$. The *edge tester* picks a uniformly random edge of the cube and rejects iff it is violated. It accepts monotone functions with probability $1$, and if $f$ is at relative distance $\varepsilon$ from every monotone function then the fraction of violated edges is at least $\varepsilon/n$, so $O(n/\varepsilon)$ repetitions reject with probability at least $2/3$.

## Proof sketch

Sorting operators: for each direction $i$, swapping the values on violated edges in direction $i$ does not increase the number of violated edges in other directions. Applying them for all directions makes $f$ monotone after changing at most $2$ values per violated edge, so the distance is at most $2 \cdot \#\text{violated}/2^n$, which yields the bound up to the constant in the number of edges $n 2^{n-1}$.

## Depends on

- [Relative Hamming distance on the Boolean cube](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/bool-dist.md)

## Sources

- O. Goldreich, S. Goldwasser, E. Lehman, D. Ron and A. Samorodnitsky, "Testing Monotonicity", Combinatorica 20(3), 2000.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
