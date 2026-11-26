# Homomorphism testing over finite abelian groups and plurality correction

Let $G, H$ be finite abelian groups and $f : G \to H$. Let $\varepsilon = \Pr_{x, y}[f(x) + f(y) \ne f(x + y)]$ with $x, y$ uniform and independent, and let $\delta$ be the minimum over homomorphisms $\phi$ of $\Pr_x[f(x) \ne \phi(x)]$. Then: (1) for every $x$ the plurality value $g(x)$ of $f(x + y) - f(y)$ over uniform $y$ has frequency at least $1 - 2\varepsilon$; (2) if $\varepsilon < 1/6$ then $g$ is a homomorphism and $\Pr_x[f(x) \ne g(x)] \le 2\varepsilon$; (3) unconditionally $\varepsilon \ge \min(1/6,\ \delta/2)$ (Goldreich 2008, Exercise 9.21).

## Proof sketch

For fixed $x$, two independent votes $f(x+y) - f(y)$ and $f(x+z) - f(z)$ agree unless one of two relations sampled from uniformly distributed pairs fails, which happens with probability at most $2\varepsilon$, so some value has mass at least $1 - 2\varepsilon$. When this mass exceeds $2/3$, $g(x) + g(y) = g(x + y)$ follows by a union bound over three such relations, and $f$ disagrees with $g$ only where its own vote loses, at most a $2\varepsilon$ fraction.

## Depends on

- [Blum–Luby–Rubinfeld linearity test](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)

## Sources

- M. Blum, M. Luby and R. Rubinfeld, "Self-Testing/Correcting with Applications to Numerical Problems", Journal of Computer and System Sciences 47(3), 1993.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
