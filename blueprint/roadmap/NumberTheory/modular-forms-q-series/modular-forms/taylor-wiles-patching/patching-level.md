# Level of a Taylor–Wiles patching datum

Let $\mathcal{O}$ be a commutative ring, $r$ a natural number, $R$ a commutative
$\mathcal{O}$-algebra, $M$ an $R$-module, $S = \mathcal{O}[[X_1, \dots, X_r]]$ the power series
ring in $r$ variables over $\mathcal{O}$, and $J \subseteq S$ an ideal. A level of a Taylor–Wiles
patching datum with relation ideal $J$ consists of:

- an $S$-module $N$;
- an $\mathcal{O}$-algebra endomorphism $\varphi \colon S \to S$;
- a surjective $\mathcal{O}$-algebra homomorphism $\psi \colon S \to R$ with
  $\psi(\varphi(X_i)) = 0$ for $i = 1, \dots, r$;
- a surjective additive map $\pi \colon N \to M$ that is $\psi$-semilinear, that is,
  $\pi(s x) = \psi(s) \pi(x)$ for $s \in S$ and $x \in N$, and whose kernel is the submodule
  $\ker \pi = (\varphi(X_1), \dots, \varphi(X_r)) N$;
- a natural number $d$ and elements $b_1, \dots, b_d \in N$ such that every $x \in N$ can be
  written as $x = \sum_{i=1}^{d} \varphi(c_i) b_i$ with $c_1, \dots, c_d \in S$, and such that for
  all $c_1, \dots, c_d \in S$ one has $\sum_{i=1}^{d} \varphi(c_i) b_i = 0$ if and only if
  $c_i \in J$ for every $i$.

In particular $N$ is generated as an $S$-module by $b_1, \dots, b_d$.
