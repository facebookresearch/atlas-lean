# Lunnon's dimension decomposition for fixed polycubes

Let $d$ and $n$ be natural numbers
with $n > 1$, let $A_d(n)$ be the number of fixed $n$-cell polycubes in dimension $d$, and for
each $i$ let $\mathrm{DX}(n,i)$ be the number of fixed $n$-cell polycubes proper in dimension $i$.
Then

$$A_d(n) = \sum_{i=1}^{n-1} \binom{d}{i} \, \mathrm{DX}(n,i).$$

The hypothesis $n > 1$ is needed: the printed formula omits its domain and fails at $n = 1$,
where the single cell is a polycube proper in dimension $0$ and so is counted only by the
$i = 0$ term, which the sum excludes. For $n > 1$ that term vanishes, since
$\mathrm{DX}(n,0) = 0$.

## Sources

- Sebastian Luther and Stephan Mertens, *The Perimeter of Proper Polycubes*, Journal of Integer Sequences 20 (2017), Article 17.9.5, Section 1, equation (1) (Lunnon's formula), with the notation $\mathrm{DX}(n, i)$ and the remark that a polycube of size $n$ spans at most $n - 1$ dimensions, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Mertens/mert4.pdf>. Original: W. F. Lunnon, *Counting multidimensional polyominoes*, Comput. J. 18 (1975), 366–367. For $\mathrm{DX}(n, 0) = 0$ when $n > 1$: Andrei Asinowski, Gill Barequet, Ronnie Barequet, and Günter Rote, *Proper n-Cell Polycubes in n − 3 Dimensions*, Journal of Integer Sequences 15 (2012), Article 12.8.4, Section 8, <https://cs.uwaterloo.ca/journals/JIS/VOL15/Barequet/barequet2.pdf>.
