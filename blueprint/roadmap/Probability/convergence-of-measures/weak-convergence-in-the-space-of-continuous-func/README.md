# Weak convergence in the space of continuous functions

Let $T > 0$, and let $\mu_n$ ($n \in \mathbb{N}$) and $\mu$ be probability measures on the space $C([0, T], \mathbb{R})$ of continuous functions with the topology of uniform convergence and its Borel $\sigma$-algebra. If the family $\{\mu_n\}$ is tight and, for every finite set $I \subseteq [0, T]$, the finite-dimensional laws of $\mu_n$ (the image measures under $f \mapsto (f(t))_{t \in I}$) converge weakly to those of $\mu$, then $\mu_n$ converges weakly to $\mu$.

## Idea

Convergence of finite-dimensional laws alone is not enough in a space of paths. Let $z_n$ be the tent function that rises from $0$ at $t = 0$ to $1$ at $t = 1/n$ and returns to $0$ at $t = 2/n$; the point masses at $z_n$ have finite-dimensional laws converging to those of the point mass at the zero function, yet $\sup |z_n| = 1$, so they do not converge weakly. Tightness rules out such escaping peaks. The proof: by Prokhorov's theorem, every subsequence has a further subsequence converging weakly to some probability measure; by the continuous mapping theorem that limit has the finite-dimensional laws of $\mu$; and finite-dimensional laws determine a law on continuous paths, so every limit is $\mu$. This is the route to Donsker's invariance principle.

## Statements

- [Tightness plus finite-dimensional convergence gives weak convergence](tendsto-continuous-path-of-tight-of-fins.md)
- [Continuous-path laws are determined by finite-dimensional marginals](continuous-path-measure-ext-of-finset-ev.md): lemma used in the proof of the main statement

## Background

- [Tight families of probability measures](../tightness-of-probability-measures/README.md)
