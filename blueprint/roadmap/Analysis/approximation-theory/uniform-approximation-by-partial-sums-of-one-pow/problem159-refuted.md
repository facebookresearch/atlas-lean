# Scottish Book Problem 159 has a negative answer

There is no sequence of real numbers
$a_0, a_1, a_2, \dots$ with the following property: for every $\varepsilon > 0$ there is a natural
number $N$ such that for every function $f : \mathbb{R} \to \mathbb{R}$ that is continuous on
$[0, 1]$ and satisfies $f(0) = 0$ and $0 \le f(x) \le 1$ for all $x \in [0, 1]$, there is a natural
number $n \le N$ with $\left|f(x) - \sum_{k=0}^{n} a_k x^k\right| < \varepsilon$ for all
$x \in [0, 1]$.

Sternbach's argument in the addendum Ad 159 uses the functions $\sin^2(2^n \pi x)$. Mazur showed
that for an arbitrary family $\Phi$ of functions of this kind, a power series with this property
exists exactly when the functions of $\Phi$ are equicontinuous.

## Sources

- S. Ruziewicz, Problem 159 of the Scottish Book; Ad 159 in the typescript (Sternbach's negative argument; Mazur's equicontinuity criterion).
