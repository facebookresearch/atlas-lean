# Upper bound lemma on a finite abelian group

Let $G$ be a finite abelian group, $U$ the uniform distribution on $G$ and $P : G \to \mathbb{R}$
a function of total mass $\sum_x P(x) = 1$. With $\hat P(\psi) = \sum_x \psi(x) P(x)$ the
discrete Fourier transform at a character $\psi : G \to \mathbb{C}$,

$$4\,\|P - U\|_{TV}^2 \le \sum_{\psi \ne 1} |\hat P(\psi)|^2,$$

the sum running over the non-trivial characters, and $\|P - U\|_{TV} = \tfrac12 \sum_x |P(x) - U(x)|$.
No positivity of $P$ is needed.

The proof is Diaconis's: by Cauchy–Schwarz, $(\sum_x |P(x) - U(x)|)^2 \le |G| \sum_x (P(x) - U(x))^2$;
by Plancherel the right side is $\sum_\psi |\hat P(\psi) - \hat U(\psi)|^2$; finally
$\hat P(1) = \hat U(1) = 1$ and $\hat U(\psi) = 0$ for $\psi \ne 1$. For $G = \mathbb{Z}/n$ this is
Lemma 2.1 of the Saint-Flour notes. It is the abelian case of the
[upper bound lemma](upper-bound-lemma.md) on a general finite group, where all irreducible
representations are one-dimensional.

## Background

- [Total variation distance of functions on a finite set](../../markov-chains/mixing-times-of-markov-chains/tv-dist.md): the
  distance being bounded.
- [Plancherel formula on a finite abelian group](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-transform-on-finite-abelian-groups/dft-plancherel.md):
  the identity behind the second step.

## Sources

- P. Diaconis, *Applications of non-commutative Fourier analysis to probability problems*,
  Saint-Flour lecture notes, Lecture Notes in Math. 1362 (1988), Lemma 2.1 and Lemma 4.2.
