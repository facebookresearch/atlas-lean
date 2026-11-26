# Hausdorff's absolute continuity criterion

Let $\mu$ be a probability measure on
$\mathbb{R}^d$ with $\mu(\mathbb{R}^d \setminus I^d) = 0$, where $I^d = [0,1]^d$ is the closed
unit cube, and let $\lambda$ be Lebesgue measure restricted to $I^d$. For a measure $\rho$ write
$m_\rho(n) = \int_{I^d} x^n \, d\rho(x)$ for its moments, indexed by multi-indices
$n \in \mathbb{N}^d$. Then $\mu$ is uniformly absolutely continuous with respect to $\lambda$ if
and only if there is a real constant $C$ such that
$(\Delta^k m_\mu)_n \le C \, (\Delta^k m_\lambda)_n$ for all multi-indices $k \le n$
(coordinatewise), where $\Delta^k$ is the iterated backward difference.

Knill compares the moments of two probability measures on the cube. Taking the second
measure to be $\lambda$ gives this criterion, with bounded density expressed as
$\mu \le M\lambda$ for some $M \ge 0$.

## Sources

- O. Knill, *Some fundamental theorems in mathematics*, §115 “Moments”, p. 52, paragraph following
  the Hausdorff–Hildebrandt–Schoenberg theorem.
  [arXiv:1807.08416v4](https://arxiv.org/pdf/1807.08416v4#page=52)
- For background on the interval moment problem see F. Hausdorff, *Summationsmethoden und
  Momentfolgen I, II* (1921) and *Momentprobleme für ein endliches Intervall* (1923), and
  Shohat–Tamarkin, *The Problem of Moments*.
- Problem `hausdorff_absolute_continuity` of the lean-eval benchmark.
