# Backward error of an approximate solution

Let $A$ be a bounded operator on an inner product space, $b$ a vector and $\hat x \ne 0$ an approximate
solution of $Ax = b$, with residual $r = A\hat x - b$. The smallest $\|E\|$ such that
$(A + E)\hat x = b$ is $\|r\|/\|\hat x\|$, attained by $E = -r\,\hat x^*/\|\hat x\|^2$, a perturbation of rank
at most one (zero when $r = 0$).

## Idea

The forward error compares $\hat x$ with the true solution, which is unknown; the backward error asks
how much the data must change for $\hat x$ to be exact, and it can be computed from the residual. Any
$E$ with $(A + E)\hat x = b$ satisfies $E \hat x = -r$, so $\|E\| \ge \|r\|/\|\hat x\|$, and the perturbation
above attains this. So $\hat x$ exactly solves a nearby system when $\|r\|/\|\hat x\|$ is small, and, for $\|A\| > 0$,
relative to the data when $\|r\|/(\|A\|\,\|\hat x\|)$ is. A small residual alone is not enough: for $A = [1]$,
$\hat x = \varepsilon$ and $b = 2\varepsilon$, the residual tends to $0$ with $\varepsilon$ while the least
perturbation has norm $1$. An algorithm is backward stable when its computed solutions always have a
small relative backward error, uniformly in the data; the condition number then bounds its forward error.

## Statements

- [Backward error of an approximate solution](is-least-norm-backward-error.md)
