# Alternating binomial transform of the squared harmonic numbers

For a complex number
$z$ and $k \in \mathbb{N}$ write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ (the empty product
being $1$), and let $H_k = 1 + \frac{1}{2} + \cdots + \frac{1}{k}$ be the $k$-th harmonic number.
Let $s$ be a complex number that is not a negative integer, and let $n \ge 1$. Then

$$
\sum_{k=1}^{n} (-1)^k \binom{s+n}{k} H_k^2 =
(-1)^n \binom{s+n-1}{n} \left(H_n^2 + \frac{2 H_n}{s+n} + \frac{2}{(s+n)^2}\right) +
\frac{H_n}{s+n} - \frac{2}{(s+n)^2} -
\frac{s}{s+n} \sum_{k=1}^{n} \frac{(-1)^k \binom{s+k-1}{k-1}}{k^2 \binom{n}{k}}.
$$

## Sources

- Necdet Batır, "Finite Binomial Sum Identities with Harmonic Numbers," Journal of Integer Sequences 24 (2021), Article 21.4.3, Theorem 7 (label `Theorem7`), equation (2.12), lines 287–293, https://cs.uwaterloo.ca/journals/JIS/VOL24/Batir2/batir13.tex
