# Smolensky: parity is far from low-degree polynomials over fields of characteristic ≠ 2

Let $\mathbb{F}$ be a field in which $2$ is invertible and let $p : \{0,1\}^n \to \mathbb{F}$ have degree at most $D$. Then $p$ agrees with the parity $x \mapsto (-1)^{|x|}$ (or with $\bigoplus_i x_i$ embedded in $\mathbb{F}$) on at most $\sum_{j \le n/2 + D}\binom{n}{j}$ inputs. In particular for $D = o(\sqrt n)$ the agreement is at most $\frac12 + o(1)$ of the cube, which is the core of the Razborov–Smolensky lower bound for $\mathrm{AC}^0[p]$ circuits computing parity.

## Proof sketch

On the agreement set $A$, every function $g : A \to \mathbb{F}$ is (after the change of variables $y_i = 1 - 2x_i$) a polynomial of degree at most $n/2 + D$: write $g$ as a multilinear polynomial and replace each monomial $y_S$ with $|S| > n/2$ by $\pm\, \mathrm{par}\cdot y_{[n]\setminus S}$, using $\mathrm{par} = p$ on $A$. Counting dimensions gives $|A| \le \dim\{\deg \le n/2 + D\}$.

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)
- [Dimension of the space of low-degree functions](dimension-of-low-degree-functions.md)

## Sources

- R. Smolensky, "Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity", STOC 1987.
- A. A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR 41(4), 1987.
