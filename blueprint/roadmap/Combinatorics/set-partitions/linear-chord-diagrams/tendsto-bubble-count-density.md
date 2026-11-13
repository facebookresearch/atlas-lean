# Limiting density of bubble sizes in linear chord diagrams

Let $B_{n,p}$ be the total
number of bubbles of size $p$ over all linear chord diagrams on $2n$ vertices. Let $x$ be a real
number with $0 < x \le 2$, and let $(p_n)_{n \ge 0}$ be natural numbers with $p_0 = 0$,
$p_n \le 2n - 2$ for every $n \ge 1$, and $p_n / (n - 1) \to x$ as $n \to \infty$. Then

$$\frac{(n-1)\,B_{n,p_n}}{\sum_{p=1}^{2n-2} B_{n,p}} \to \frac{e\,(6-x)}{2\,(4e-2)}\,e^{-x/2}$$

as $n \to \infty$. The sum in the denominator leaves out the bubble sizes $2n - 1$ and $2n$; a
bubble of size $2n$ is a whole diagram without short chords.

The paper writes $B_{n,x(n-1)}$; since $x(n-1)$ need not be an integer, the limit is read along
integer sizes $p_n$ with $p_n/(n-1) \to x$, the scaling the paper's proof uses.

## Sources

- Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer Sequences 27 (2024), Article 24.4.2, Theorem 6 (`jis-2024-24.4.2-thm-6`).
