# Volume reduction of the ellipsoid method

For $n \ge 2$,

$$
\frac{n}{n+1}\Bigl(\frac{n^2}{n^2-1}\Bigr)^{(n-1)/2} < e^{-1/(2(n+1))} .
$$

Apply $1 + x < e^x$ for $x \ne 0$ twice: to $x = -1/(n+1)$, giving $\frac{n}{n+1} < e^{-1/(n+1)}$, and to $x = 1/(n^2 - 1)$, giving $\frac{n^2}{n^2-1} < e^{1/(n^2-1)}$. Raising the second to the power $(n-1)/2 > 0$ gives $e^{1/(2(n+1))}$, and $e^{-1/(n+1)} e^{1/(2(n+1))} = e^{-1/(2(n+1))}$. This is the algebraic core of the volume lemma; the geometric statement is the [volume lemma](volume-next-ellipsoid-lt.md).

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, Lemma 7.1 and its proof.
