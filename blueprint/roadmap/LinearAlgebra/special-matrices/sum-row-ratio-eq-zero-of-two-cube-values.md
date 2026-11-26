# Cube-fiber cancellation for order-six complex Hadamard matrices

Suppose a complex
$6\times6$ matrix $H$ and its entrywise square both have unit-modulus entries and satisfy
$A^*A=6I$. Fix two distinct rows $i,j$ and set $r_k=H_{ik}\overline{H_{jk}}$.
If $a,b$ are distinct complex numbers and every $r_k^3$ equals either $a$ or $b$, then
$\sum_{k:r_k^3=a}r_k=0$. Neither fiber is required to be nonempty.

## Sources

- OpenAI, [Hadamard cube-fiber comparator](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HadamardCubeFiber.lean#L9-L34).
