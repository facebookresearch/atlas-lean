# Touchard's Catalan identity

For every natural number $n$, writing
$C_k = \binom{2k}{k}/(k+1)$ for the $k$-th Catalan number,

$$C_{n+1} = \sum_{i=0}^{\lfloor n/2 \rfloor} \binom{n}{2i} 2^{n-2i} C_i.$$

## Sources

- https://cs.uwaterloo.ca/journals/JIS/VOL20/Dershowitz/dersh3.tex, lines 274-277. A second JIS source prints the finite upper bound as `floor(n/2)`.
